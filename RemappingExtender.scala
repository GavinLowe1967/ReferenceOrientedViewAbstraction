package ViewAbstraction

import RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}
import ox.gavin.profiling.Profiler

/** Class that extends a result-defining map to a full mapping. */
class RemappingExtender(trans: Transition, cv: ComponentView){
  /* Relationship of main functions.
   * makeExtensions
   * |--makeExtensionsNew
   *    |--findLinkage
   *    |--RemappingExtender.anyLinkageC
   *    |--getCompressedCandidatesMap
   *    |--mapUndefinedToFresh
   *    |--extendForLinkage
   *       |--extendMapByIndex
   *       |--makeExtensionsNew
   * 
   * extendMapOverComponent 
   *   (called from SingleRefEffectOnUnification.makeSecondaryInduced) 
   */

  require(singleRef)

  Profiler.count("RemappingExtender")

  /* A few object variables, extracted directly from pre and cv, used in
   * several functions. */
  @inline private def pre = trans.pre; 
  @inline private def post = trans.post
  @inline private def preCpts = pre.components;
  @inline private def cpts = cv.components

  // IDs of components in pre, cv
  @inline private def preCptIds = pre.cptIdsBitMap _
  @inline private def cptIds(t: Type)(id: Identity) = 
    // cv.cptIdsBitMapX(t)(id)
    IdentitiesBitMap.get(cv.cptIdsBitMap, t, id)

  /** Temporary test to help with debugging.  Might this be the instance causing
    * problems? */
  @inline private def highlight = false && // IMPROVE
    pre.servers.servers(1).cs == 34 && 
    preCpts.length == 2 && cpts.length == 2 &&
      preCpts(0).cs == 23 && preCpts(1).cs == 15 && 
      cpts(0).cs == 24 && cpts(1).cs == 11 && cpts(0).ids(2) == 2

  /** Bound on the parameters of cpts.  If NewEffectOnStore3 then ignoring
    * secondary. */
  // private val paramsBound = {
  //   val pb = pre.servers.paramsBound.clone
  //   for(i <- 0 until (if(NewEffectOnStore3) 1 else cpts.length); 
  //       t <- 0 until numTypes)
  //     pb(t) = pb(t) max cpts(i).getParamsBound(t)
  //   pb
  // }

  import Unification.UnificationList // = List[(Int,Int)]

  /** Representation of a linkage.  A pair (i, j) represents a linkage between
    * cpts(i) and preCpts(j). */
  import RemappingExtender.Linkage //  = (Int,Int)

  /** The result returned by makeExtensions.  Each map is paired with the
    * representation of the cross references it creates for condition (b). */
  import RemappingExtender.ExtensionsInfo
  // = ArrayBuffer[(RemappingMap, CompressedCandidatesMap)]

  /** For each parameter, the list of identities it can be mapped to when
    * forming all completions. */
  import RemappingExtender.CandidatesMap //  = Array[Array[List[Identity]]]

  @inline private def recycle(map: RemappingMap) = Pools.returnRemappingRows(map)

  /** Find a linkage for part (b) implied by rdMap, excluding those already in
    * doneB; or null if none exists.  A pair (i, j) such that for some
    * parameter id of cpts(i), id1 = rdMap(id) is a parameter of preCpts(j),
    * with one of those being the identity; and such this doesn't represent a
    * unification of components (with identities id/id1). */
// IMPROVE: represent doneB by a bitmap.  And store which (t,id1) pairs have
// already been considered for this unifs, rdMap (?)
  private def findLinkage(
    unifs: UnificationList, rdMap: RemappingMap, doneB: List[Linkage])
      : Linkage = {
    // Bitmaps giving indices of unified cpts in cv, resp, pre
    val cvUnifs = new Array[Boolean](cpts.length)
    val preUnifs = new Array[Boolean](preCpts.length)
    var us = unifs
    while(us.nonEmpty){
      val (i,j) = us.head; us = us.tail; cvUnifs(i) = true; preUnifs(j) = true
    }
    var result: Linkage = null // final result when non-null

    // Iterate through rdMap
    var t = 0
    while(t < numTypes && result == null){
      var id = 0; val len = rdMap(t).length
      while(id < len && result == null){
        val id1 = rdMap(t)(id)
        if(id1 >= 0){
          // The index in preCpts of the component with identity (t,id1),
          // or -1 if no such.
          val idJ = pre.idsIndexMap(t)(id1)
          if(idJ >= 0 && !preUnifs(idJ)){
            // Find all i such that id is a reference of cpts(i), not unified
            var i = 0
            while(i < cpts.length && result == null){
              if(!cvUnifs(i) && cpts(i).hasRef(t,id) && !contains(doneB,(i,idJ)))
                result = (i,idJ) 
              i += 1
            }
          }
          if(result == null){
            // All indices of components of pre that have (t,id1) as a
            // reference (or null if there are no such).
            var refJs: ByteBitMap.ByteBitMap = pre.refsIndexMap(t)(id1) 
            if(refJs != ByteBitMap.Empty){
              // Index of component in cv with identity (t,id), or -1 if no such.
              val i = cv.idsIndexMap(t)(id)
              // If not unified, we have a linkage i->j for j in refJs
              if(i >= 0 && !cvUnifs(i)){
                val iter = ByteBitMap.iterator(refJs)
                // var ix = 0 // index into refJs
                // while(ix < refJs.length /*refJs.nonEmpty*/ && result == null){
                //  val j = refJs(ix); ix += 1
                while(iter.hasNext && result == null){
                  val j = iter.next()
                  if(!preUnifs(j) && !contains(doneB,(i,j))) result = (i,j)
                }
              }
            }
          } // end of if(result == null)
        }
        id += 1
      } // end of inner while
      t += 1
    } // end of while
    result
  }

  /** Linkages for condition (c).  All missing references of cv.principal that
    * map under rdMap to a missing reference of pre.principal. 
    * 
    * Note: not currently used (except for testing). */
  private def findLinkagesC(rdMap: RemappingMap): ArrayBuffer[Parameter] = {
    val result = new ArrayBuffer[Parameter]
    // Linkages for condition (c).  Iterate through parameters of
    // cv.principal.
    val cvPrincParams = cv.principal.processIdentities; var i = 1
    while(i <  cvPrincParams.length){
      val (t,id) = cvPrincParams(i); i += 1
      // Is id a missing parameter for cv?
      if(!isDistinguished(id) && !cptIds(t)(id)){
        val id1 = rdMap(t)(id)
        // Is id1 a missing parameter for pre?
        if(id1 >= 0 && preCpts(0).processIdentities.contains((t,id1)) &&
            !preCptIds(t)(id1))
          result += ((t,id))
      }
    }
    result
  }

  /** Extend map to map all undefined values to distinct fresh values. */
  @inline private def mapUndefinedToFresh(map: RemappingMap) =
    Remapper.mapUndefinedToFresh(map, trans.getNextArgMap)
    // IMPROVE: above clones the NextArgMap, unnecessarily

  /** Given a result-defining map rdMap that creates a linkage between c1 =
    * cpts(i) and c2 = preCpts(j), find all extensions that maps each
    * parameter of c1 to a parameter of c2, or not; but avoiding mapping to
    * elements of resultRelevantParams.  */
// FIXME: but if this is a secondary reference, can map x -> y if x is not a
// parameter of v.princ, for y in resultRelevantParams.
  private def extendForLinkage(
    rdMap: RemappingMap, resultRelevantParams: BitMap, 
    i: Int, j: Int, isPrimary: Boolean, doneB: List[Linkage])
      : ArrayBuffer[RemappingMap] = {
    val c1 = cpts(i); val c2 = preCpts(j); val c2Params = c2.processIdentities
    // Create otherArgMap containing all params of c2 not in range rdMap
    val otherArgs = Remapper.newOtherArgMap
    /* Should parameter (t,id) be included in otherArgs? */
    // IMPROVE: memoise some of this.
    @inline def include(t: Type, id: Identity) = (
      !isDistinguished(id) &&
        (!resultRelevantParams(t)(id) || 
          !isPrimary && !cpts(0).hasParam(t,id)) &&
        !rdMap(t).contains(id)
    )
    for(ix <- 0 until c2.length){
      val (t,id) = c2Params(ix)
      if(include(t,id) && !otherArgs(t).contains(id))
        otherArgs(t) ::= id
    }
    // For each non-distinguished parameter (t,x) of c1, the values (t,y) that
    // (t,x) can be mapped to: elements of otherArgs(t) such that for each
    // (ii,jj) in doneB, if (t,x) is a parameter of cv.cpts(ii), then (t,y) is
    // not a parameter of preCpts(jj); and not mapping an identity to an
    // identity.  Indexed following the indices of parameters in c1.
    val candidates = new Array[List[Identity]](c1.length)
    for(ix <- 0 until c1.length){
      val (t,x) = c1.processIdentity(ix)
      // Can (t,x) be mapped to (t,y)?
      @inline def respects(y: Identity) = {
        var db = doneB; var ok = !(cptIds(t)(x) && preCptIds(t)(y))
        while(db.nonEmpty && ok){
          val (ii,jj) = db.head; db = db.tail
          if(cpts(ii).hasParam(t,x) && preCpts(jj).hasParam(t,y)) ok = false
        }
        ok
      }
      if(!isDistinguished(x) && rdMap(t)(x) < 0)
        candidates(ix) = otherArgs(t).filter(respects)
    } // end of for loop over ix
    extendMapByIndex(rdMap, c1, candidates)
  }

  /** Extend map over the parameters of c in all possible ways, mapping the
    * parameter with index ix to an element of candidates(ix), or not.  map is
    * mutated, but all updates are rolled back. */
  private def extendMapByIndex(
    map: RemappingMap, c: State, candidates: Array[List[Identity]])
      : ArrayBuffer[RemappingMap] = {
    val result = new ArrayBuffer[RemappingMap] // builds result
    val addedParams = Pools.getBitMap  // Parameters that we have added to map

    /* Extend map over parameters of c from index ix onwards. */
    def rec(ix: Int): Unit = {
      if(ix == c.length) result += Remapper.cloneMap(map)
      else{
        val(t,x) = c.processIdentity(ix)
        if(!isDistinguished(x) && map(t)(x) < 0){
          // Try mapping x to each element of candidates(ix)
          var cands = candidates(ix)
          while(cands.nonEmpty){
            val y = cands.head; cands = cands.tail
            if(!addedParams(t)(y)){
              //assert(!map(t).contains(y) && !(cptIds(t)(x) && preCptIds(t)(y)))
              map(t)(x) = y; addedParams(t)(y) = true  // temporary update (+)
              rec(ix+1)
              map(t)(x) = -1; addedParams(t)(y) = false // backtrack (+)
            }
          }
        }
        // Also leave (t,x) unmapped
        rec(ix+1)
      } // end of else
    }

    rec(0); Pools.returnBitMap(addedParams); result
  }

//   /** Build map showing what each parameter of cv can be mapped to so as to be
//     * consistent with rdMap (so giving List() on parameters in dom rdMap, and
//     * not mapping to an element of range rdMap) and resultRelevantParams (not
//     * mapping to any such parameter) and respecting doneB (for each (i,j) in
//     * doneB, not mapping any parameter of cv.cpts(i) to a component of
//     * pre.cpts(j)).   */
//   private def getCandidatesMap(
//     resultRelevantParams: BitMap, rdMap: RemappingMap, doneB: List[Linkage])
//       : CandidatesMap = {
//     assert(singleRef && !useNewEffectOnStore)
// //println("rdMap = "+Remapper.show(rdMap))
//     // All params of pre, except those in resultRelevantParams or range rdMap 
// // IMPROVE: memoise at least some of this
// //println(pre.getAllParams(0))
//     val otherArgs: Array[List[Identity]] = Array.tabulate(numTypes)(t => 
//       pre.getAllParams(t).filter(p => 
//         !resultRelevantParams(t)(p) && !rdMap(t).contains(p)))
// //println("otherArgs = "+otherArgs.mkString("; "))
//     // The same but excluding identities
//     val nonIds = Array.tabulate(numTypes)(t => 
//       otherArgs(t).filter(p1 => !preCptIds(t)(p1)))
//     // List of parameters that each parameter x of cv could be mapped to;
//     // empty list if x is already mapped in rdMap; otherwise relevant members
//     // of otherArgs, not mapping an identity to an identity.
//     val candidates = Array.tabulate(numTypes)(t => 
//       Array.tabulate(rdMap(t).length)(p => 
//         if(rdMap(t)(p) < 0) 
//           if(cptIds(t)(p)) nonIds(t) else otherArgs(t)
//         else List() 
//       ))
//     // For each (i,j) in doneB, for each param (t,x) of cv.cpts(i),
//     // remove all parameters of preCts(j) from the list candidates(x). 
//     for((i,j) <- doneB){
//       val preC = preCpts(j)
//       for((t,x) <- cpts(i).processIdentities; if !isDistinguished(x)){
//         candidates(t)(x) = candidates(t)(x).filter(y => !preC.hasParam(t,y))
//       }
//     }
//     candidates
//   }

  import CompressedCandidatesMap._

  /** Representation of all values to which each parameter can be mapped. */
  private def getCompressedCandidatesMap(
    resultRelevantParams: BitMap, rdMap: RemappingMap, doneB: List[Linkage])
      : CompressedCandidatesMap = {
    val typeSizes = pre.getNextArgMap
    // All params of pre, except those in resultRelevantParams or range rdMap 
    val otherArgs = new Array[Candidates](numTypes)
    // The same but excluding identities
    val nonIds = new Array[Candidates](numTypes)
    for(t <- 0 until numTypes){
      var oArgs = Empty; var nIds = Empty
      for(p <- 0 until typeSizes(t)) 
        if(!resultRelevantParams(t)(p) && !rdMap(t).contains(p)){
          oArgs = add(oArgs, p)
          if(!preCptIds(t)(p)) nIds = add(nIds,p)
        }
      otherArgs(t) = oArgs; nonIds(t) = nIds
    }
    val candidates = Array.tabulate(numTypes)(t => 
      Array.tabulate(rdMap(t).length){ p =>
        val y = rdMap(t)(p)
        if(y < 0) 
          if(cptIds(t)(p)) nonIds(t) else otherArgs(t)
        else fixed(y) // All extensions must use y here 
      })
    // For each (i,j) in doneB, for each param (t,x) of cv.cpts(i),
    // remove all parameters of preCts(j) from the list candidates(x). 
    for((i,j) <- doneB){
      val preC = preCpts(j); val preCIds = preC.ids
      for((t,x) <- cpts(i).processIdentities)
        if(!isDistinguished(x) && rdMap(t)(x) < 0){
          // Remove params of preC of type t from candidate(t)(x)
          for(k <- 0 until preCIds.length; if preC.typeMap(k) == t){
            val y = preCIds(k)
            if(!isDistinguished(y))
              candidates(t)(x) = remove(candidates(t)(x), y)
          }
        }
    }
    candidates.flatten
    // IMPROVE: create in flattened form?
  } 

  // /** Implementation of allExtensions from the paper.  All extensions of rdMap,
  //   * mapping undefined parameters to an arbitrary parameter of pre, or the
  //   * next fresh parameter, but not to parameters of resultRelevantParams, and
  //   * only consistently with doneB.  Add each to extensions. */
  // private def allExtensions(
  //   resultRelevantParams: BitMap, rdMap: RemappingMap, 
  //   doneB: List[Linkage], extensions: ExtensionsInfo)
  //     : Unit = {
  //   require(!useNewEffectOnStore)
  //   Profiler.count("allExtensions")
  //   // All parameters that each parameter can be mapped to
  //   val candidates = getCandidatesMap(resultRelevantParams, rdMap, doneB)
  //   // Build all extensions of rdMap, mapping each parameter to each element
  //   // of candidates(x), or not, injectively.
  //   val eMaps = RemappingExtender.extendMapToCandidates(
  //     rdMap, candidates, pre.getNextArgMap)
  //   // Map remainder to fresh variables, and add to extensions.
  //   var i = 0
  //   while(i < eMaps.length){
  //     val eMap = eMaps(i); i += 1
  //     mapUndefinedToFresh(eMap)
  //     maybeAdd(extensions, eMap) 
  //     Profiler.count("allExtensions - add")
  //   }
  // }


  @inline private def maybeAdd(extensions: ExtensionsInfo,
    map: RemappingMap, candidatesMap: CompressedCandidatesMap)
      : Unit = {
    require(candidatesMap != null)
    /* Does extensions(i) equal (map, candidatesMap)? */
    // def matches(i: Int) = {
    //   val (map1, cands1) = extensions(i)
    //   Remapper.equivalent(map, map1) &&
    //     RemappingExtender.equalCandidatesMaps(candidatesMap, cands1)
    // }
    // Search for repetitions ... doesn't seem to happen
    // var ix = 0; while(ix < extensions.length && !matches(ix)) ix += 1 
    // if(ix == extensions.length) 
    extensions += ((map, candidatesMap))
    // else Profiler.count("RemappingExtender.maybeAdd repeat")
  }

  @inline def maybeAdd(extensions: ExtensionsInfo, map: RemappingMap): Unit = {
    var ix = 0
    while(ix < extensions.length && !Remapper.equivalent(extensions(ix)._1, map))
      ix += 1
    if(ix == extensions.length) extensions += ((map,null))
    else recycle(map)
  }

  /** Implementation of makeExtensions from the paper.  Create all required
    * extensions of result-defining map rdMap.  Note: rdMap may be mutated and
    * included in the result; otherwise it is recycled. */
  def makeExtensions(unifs: UnificationList, resultRelevantParams: BitMap, 
    rdMap: RemappingMap, isPrimary: Boolean)
      : ExtensionsInfo = {
    require(useNewEffectOnStore)
    val extensions = new ExtensionsInfo
    //if(useNewEffectOnStore)
      makeExtensionsNew(
        unifs, resultRelevantParams, rdMap, List(), isPrimary, extensions)
    // else 
    //   makeExtensions1(
    //     unifs, resultRelevantParams, rdMap, List(), isPrimary, extensions)
    extensions
  }  

  // /** Implementation of makeExtensions from the paper.  Create all required
  //   * extensions of result-defining map rdMap.  Add all such to extensions.
  //   * doneB gives the instances of condition (b) that we have dealt with so
  //   * far.  Note: rdMap may be mutated and might be included in result; but
  //   * otherwise should be recycled. */
  // private def makeExtensions1(
  //   unifs: UnificationList, resultRelevantParams: BitMap, 
  //   rdMap: RemappingMap, doneB: List[Linkage], 
  //   isPrimary: Boolean, extensions: ExtensionsInfo)
  //     : Unit = {
  //   require(!useNewEffectOnStore)
  //   // if(highlight)println("makeExtensions1; rdMap = "+Remapper.show(rdMap)+
  //   //   s"; doneB = $doneB")
  //   val linkagesC = RemappingExtender.anyLinkageC(rdMap, cv, pre)
  //   if(linkagesC){
  //     allExtensions(resultRelevantParams, rdMap, doneB, extensions)
  //     recycle(rdMap)
  //   }
  //   else{
  //     val newLinkage = findLinkage(unifs, rdMap, doneB) 
  //     if(newLinkage == null){ 
  //       mapUndefinedToFresh(rdMap)   // map remaining params to fresh
  //       maybeAdd(extensions, rdMap) 
  //       // Add to extensions if not there already
  //     }
  //     else{
  //       val (i,j) = newLinkage
  //       val extendedMaps = 
  //         extendForLinkage(rdMap, resultRelevantParams, i, j, isPrimary, doneB)
  //       var k = 0
  //       while(k < extendedMaps.length){
  //         val eMap = extendedMaps(k); k += 1
  //         makeExtensions1(unifs, resultRelevantParams, eMap, 
  //           (i,j)::doneB, isPrimary, extensions)
  //       }
  //       recycle(rdMap)
  //     }
  //   }
  // }

  /** Implementation of makeExtensions from the paper.  Create extensions
    * necessary for considering missing cross references (condition (b)), but
    * don't consider common missing references (condition (c) yet.  Note:
    * rdMap may be mutated and might be included in result; but otherwise
    * should be recycled. */
  private def makeExtensionsNew(
    unifs: UnificationList, resultRelevantParams: BitMap, 
    rdMap: RemappingMap, doneB: List[Linkage], 
    isPrimary: Boolean, extensions: ExtensionsInfo)
      : Unit = {
    val newLinkage = findLinkage(unifs, rdMap, doneB)
    if(newLinkage == null){      // Add to extensions if not already there. 
      if(RemappingExtender.anyLinkageC(rdMap, cv, trans.pre)){
        val candidates = 
          getCompressedCandidatesMap(resultRelevantParams, rdMap, doneB)
        maybeAdd(extensions, rdMap, candidates)
      }
      else{ // Condition (c) satisfied vacuously. 
        Remapper.mapUndefinedToFresh(rdMap, trans.getNextArgMap)
        maybeAdd(extensions, rdMap)
      }
    }
    else{
      val (i,j) = newLinkage
      val extendedMaps =
        extendForLinkage(rdMap, resultRelevantParams, i, j, isPrimary, doneB)
      var k = 0
      while(k < extendedMaps.length){
        val eMap = extendedMaps(k); k += 1
        makeExtensionsNew(unifs, resultRelevantParams, eMap,
          (i,j)::doneB, isPrimary, extensions)
      }
      recycle(rdMap)
    }
  }

  /** Find all consistent extensions of map over the parameters of c, mapping
    * each parameter to an element of otherArgs, or not.  Each such map is
    * fresh.  map is mutated but changes rolled back.*/
  def extendMapOverComponent(map: RemappingMap, c: State, otherArgs: OtherArgMap)
      : ArrayBuffer[RemappingMap] = {
    val result = new ArrayBuffer[RemappingMap]
    val cParams = c.processIdentities

    /* Extend map over params of c1 from ix onwards, based on otherArgs. */
    def rec(ix: Int): Unit = {
      if(ix == c.length) result += Remapper.cloneMap(map)
      else{
        val (t,id0) = cParams(ix)
        if(!isDistinguished(id0) && map(t)(id0) < 0){
          val isId = cptIds(t)(id0)  // Is this an identity?
          // map (t,id0) to each element of otherArgs(t)
          var toDoIds = otherArgs(t); var doneIds = List[Identity]()
          // Inv: reverse(doneIds) ++ toDoIds = otherArgs(t)
          while(toDoIds.nonEmpty){
            val id1 = toDoIds.head; toDoIds = toDoIds.tail
            // Don't map an identity to an identity
            if(!(isId && preCptIds(t)(id1))){
              otherArgs(t) = append1(doneIds, toDoIds) // temporary update (*)
              map(t)(id0) = id1  // temporary update (+)
              rec(ix+1)
              map(t)(id0) = -1   // backtrack (+)
            }
            doneIds ::= id1 // order doesn't matter
          } // end of while loop
          otherArgs(t) = doneIds // undo (*)
        } // end of if(!isDistinguished ... )
        // Also don't map (t,i) to anything
        rec(ix+1)
      }
    } // end of rec

// // IMPROVE: if otherArgs is empty, just add rdMap
    rec(0); result
  }

  // ========= Hooks for testing

  private val outer = this

  /** Object providing hooks for testing. */
  object TestHooks{
    def findLinkages(unifs: UnificationList, rdMap: RemappingMap) = 
      outer.findLinkage(unifs, rdMap, List())
    // IMPROVE: use same names

    val findLinkagesC = outer.findLinkagesC _

    //val getCandidatesMap = outer.getCandidatesMap _
  }
}

// =======================================================

object RemappingExtender{

  /* allCompletions
   * |--allCompletions1
   * |  |--CompressedCandidatesMap.extractMap
   * |  |--CompressedCandidatesMap.toList
   * |  |--extendMapToCandidates
   * |  |--mapUndefinedToFresh
   * |--mapUndefinedToFresh
   */

  /** Representation of a linkage.  A pair (i, j) represents a linkage between
    * cpts(i) and preCpts(j). */
  type Linkage = (Int,Int)

  /** For each parameter, the list of identities it can be mapped to when
    * forming all completions. */
  type CandidatesMap = Array[Array[List[Identity]]]

  /** Are map1 and map2 equal? */
  def equalCandidatesMaps(map1: CandidatesMap, map2: CandidatesMap): Boolean = {
    if(map1 == null) map2 == null
    else if(map2 == null) false
    else{
      var t = 0; var equal = true
      while(t < numTypes && equal){
        val len = map1(t).length; assert(map2(t).length == len); var i = 0
        while(i < len && map1(t)(i) == map2(t)(i)) i += 1
        equal = i == len; t += 1
      }
      equal
    }
  }

  import CompressedCandidatesMap.CompressedCandidatesMap

  /** The result returned by makeExtensions.  Each element is a pair (map,
    * candidates), where candidates gives all ways in which undefined
    * parameters can be mapped. If candidates == null then the map is total,
    * and condition c is satisfied vacuously.  */
  // type ExtensionsInfo = ArrayBuffer[(RemappingMap, CandidatesMap)]
  type ExtensionsInfo = ArrayBuffer[(RemappingMap, CompressedCandidatesMap)]

  /** Extend rdMap, mapping each unmapped parameter (t,p) to each element of
    * candidates(t)(p) with p < paramsBound(t), or not.  Each map is fresh.
    * rdMap is mutated, but all changes are backtracked.  preParamsSizes(t)
    * gives an upper bound on the parameters of type t in candidates(t).   */
  private def extendMapToCandidates(
    rdMap: RemappingMap, candidates: Array[Array[List[Identity]]], 
    preParamSizes: Array[Int], paramsBound: Array[Int])
      : ArrayBuffer[RemappingMap] = {
    val result = new ArrayBuffer[RemappingMap]
    // bitmap showing which parameters of pre have been used in the current
    // mapping.  Calls to rec mutate this but backtrack the updates.
    val used = Array.tabulate(numTypes)(t => 
      new Array[Boolean](preParamSizes(t)))

    /* Remap from (t,i) onwards. */
    def rec(t: Type, i: Identity): Unit = {
      if(t == numTypes) result += Remapper.cloneMap(rdMap)
      else if(i == paramsBound(t) /*rdMap(t).length*/) rec(t+1,0)
      else{
        if(rdMap(t)(i) < 0){
          for(x <- candidates(t)(i); if !used(t)(x)){
            used(t)(x) = true             // temporary update (*)
            rdMap(t)(i) = x; rec(t,i+1)
            used(t)(x) = false            // backtrack (*)
          }
          rdMap(t)(i) = -1                // undo update
        }
        rec(t,i+1) // leave (t,i) unmapped
      }
    }

    rec(0,0); result
  }

  /** If rdMap applied to cv and trans.pre have a common missing reference, then
    * all completions of rdMap, mapping undefined parameters to an element of
    * the corresponding entry in candidates.  Otherwise, the effect of mapping
    * all undefined entries in rdMap to a fresh value.  rdMap is mutated, but
    * all changes are backtracked. */
  def allCompletions(rdMap: RemappingMap, candidates: CompressedCandidatesMap, 
    cv: ComponentView, trans: Transition)
      : ArrayBuffer[RemappingMap] = {
    if(candidates != null){
      val unflattened = 
        CompressedCandidatesMap.splitBy(candidates, cv.getParamsBound)
      val map1 = 
        if(rdMap == null) CompressedCandidatesMap.extractMap(unflattened) 
        else rdMap
// IMPROVE
      assert(anyLinkageC(map1, cv, trans.pre))
      // IMPROVE: maybe work directly with candidates?
      val candidates1 = unflattened.map(_.map(CompressedCandidatesMap.toList))
      // Bound on parameters of cv, ignoring secondary if NewEffectOnStore3. 
      val paramsBound = cv.servers.paramsBound.clone
      for(i <- 0 until (if(NewEffectOnStore3) 1 else cv.components.length);
          t <- 0 until numTypes)
        paramsBound(t) = paramsBound(t) max cv.components(i).getParamsBound(t)
// IMPROVE, and calculate paramsBound this way
      if(!NewEffectOnStore3) 
        for(t <- 0 until numTypes) assert(paramsBound(t) == map1(t).length)
      allCompletions1(map1, candidates1, trans, paramsBound)
    }
    else{
      // This case arises from NewEffectOn.processInducedInfoLazy, when
      // conditions (b) and (c) are already satisfied, and we still have the
      // map to hand.  In this case, the map is total
      assert(rdMap != null)
// IMPROVE
      assert(!anyLinkageC(rdMap, cv, trans.pre))
      for(t <- 0 until numTypes; x <- rdMap(t)) assert(x >= 0)
      // Note: need to clone, because NewEffectOn recycles rdMap.
      val map1 = Remapper.cloneMap(rdMap)
      // Remapper.mapUndefinedToFresh(map1, trans.getNextArgMap) already total
      ArrayBuffer(map1)
    }
  }

  /** All completions of rdMap, mapping undefined parameters to an element of
    * the corresponding entry in candidates, or a fresh value (wrt trans).
    * rdMap is mutated, but all changes are backtracked.  Only parameters
    * (t,i) with i < paramsBound(t) are updated. */
  private def allCompletions1(
    rdMap: RemappingMap, candidates: CandidatesMap, trans: Transition, 
    paramsBound: Array[Int])
      : ArrayBuffer[RemappingMap] = {
    val completions = new ArrayBuffer[RemappingMap]
    val nextArgMap = trans.getNextArgMap // IMPROVE: don't clone

    // Build all completions of rdMap, mapping each parameter to each element
    // of candidates(x), or not, injectively.
    val eMaps = extendMapToCandidates(rdMap, candidates, nextArgMap, paramsBound)
    // Map remainder to fresh variables, and add to completions.
    var i = 0
    while(i < eMaps.length){
      val eMap = eMaps(i); i += 1
      // Note: do not need fresh nextArgMap for each iteration
      Remapper.mapUndefinedToFresh(eMap, nextArgMap)
      completions += eMap
      Profiler.count("allCompletions - add")
    }
    completions
  }

  /** Extend map, mapping each unmapped identity to an identity of c, or a fresh
    * value.  Each resulting map is fresh.  map is mutated, but all changes
    * are backtracked.  */
  def extendToMissingComponent(map: RemappingMap, c: State)
      : ArrayBuffer[RemappingMap] = {
    // nextArg(t) will hold value of next fresh param of type t
    val nextArg = Array.fill(numTypes)(0)
    // Find params of c.  We expect there not to be many, so use Lists
    val candidates = Array.fill(numTypes)(List[Identity]())
    val cIds = c.processIdentities
    for(i <- 0 until cIds.length){
      val (t,x) = cIds(i)
      if(!isDistinguished(x) && !contains(candidates(t), x)){
        candidates(t) ::= x; nextArg(t) = nextArg(t) max (x+1)
      }
    }
    // bitmap showing which parameters of c have been used in the current
    // mapping.  Calls to rec mutate this but backtrack the updates.
    val used = Array.tabulate(numTypes)(t => new Array[Boolean](nextArg(t)))
    // Filter out those candidates in range of map; find next fresh param.
    for(t <- 0 until numTypes; i <- 0 until map(t).length){
      val x = map(t)(i)
      candidates(t) = candidates(t).filter(_ != x)
      nextArg(t) = nextArg(t) max (x+1)
    }
    val result = new ArrayBuffer[RemappingMap]

    /* Remap from (t,i) onwards. */
    def rec(t: Type, i: Identity): Unit = {
      if(t == numTypes){
        // Clone; map remaining to fresh; add to result
        val map1 = Remapper.cloneMap(map)
        Remapper.mapUndefinedToFresh(map1, nextArg)
        result += map1
      }
      else if(i == map(t).length) rec(t+1,0)
      else{
        if(map(t)(i) < 0){
          for(x <- candidates(t); if !used(t)(x)){
            used(t)(x) = true          // temporary update (*)
            map(t)(i) = x; rec(t,i+1)
            used(t)(x) = false         // backtrack (*)
          }
          map(t)(i) = -1               // backtrack update
        }
        rec(t,i+1)  // also leave (t,i) unmapped
      }
    }

    rec(0,0); result
  }


  /** Is there any linkage for condition (c), corresponding to rdMap? */
  @inline 
  def anyLinkageC(rdMap: RemappingMap, cv: ComponentView, pre: Concretization)
      : Boolean = {
    val cptIds = cv.cptIdsBitMap; // val preCptIds = pre.cptIdsBitMap 
    val prePrincParams = pre.components(0).processIdentities
    val cvPrincParams = cv.principal.processIdentities
    // Iterate through parameters of cv.principal.
    var i = 1; var found = false
    while(i < cvPrincParams.length && !found){
      val (t,id) = cvPrincParams(i); i += 1
      // Is id a missing parameter for cv?
      if(!isDistinguished(id) &&  !IdentitiesBitMap.get(cptIds,t,id)){
          // !cptIds(t)(id)){
        val id1 = rdMap(t)(id)
        // Is id1 a missing parameter for pre?
        if(id1 >= 0 && prePrincParams.contains((t,id1)) &&
            !pre.cptIdsBitMap(t)(id1))
          found = true
      }
    }
    found
  }

  private val outer = this

  object TestHooks1{
    val extendMapToCandidates = outer.extendMapToCandidates _

  }


}
