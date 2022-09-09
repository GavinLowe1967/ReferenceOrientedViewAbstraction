package ViewAbstraction

import RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}
import ox.gavin.profiling.Profiler

/** Class that extends a result-defining map to a full mapping. */
class RemappingExtender(trans: Transition, cv: ComponentView){
//  pre: Concretization, post: Concretization, cv: ComponentView){

  /* Relationship of main functions.
   * makeExtensions
   * |--makeExtensions1
   *    |--findLinkagesC
   *    |--allExtensions
   *    |--findLinkages
   *    |--mapUndefinedToFresh
   *    |--extendForLinkage
   *    |  |--extendMapOverComponent (also visible externally)
   */

  Profiler.count("RemappingExtender")

  /* A few object variables, extracted directly from pre and cv, used in
   * several functions. */
  @inline private def pre = trans.pre; 
  @inline private def post = trans.post
  @inline private def preCpts = pre.components;
  @inline private def cpts = cv.components

  // IDs of components in pre, cv
  @inline private def preCptIds = pre.cptIdsBitMap 
  @inline private def cptIds = cv.cptIdsBitMap 

  @inline private def preParamSizes = pre.getNextArgMap

  /** Temporary test to help with debugging.  Might this be the instance causing
    * problems? */
  @inline private def highlight = false && // IMPROVE
    pre.servers.servers(1).cs == 34 && 
    preCpts.length == 2 && cpts.length == 2 &&
      preCpts(0).cs == 23 && preCpts(1).cs == 15 && 
      cpts(0).cs == 24 && cpts(1).cs == 11 && cpts(0).ids(2) == 2

  /** A NextArgMap, containing values greater than anything in pre or post. */
  private val nextArg: NextArgMap = trans.getNextArgMap
  // pre.getNextArgMap
  // post.updateNextArgMap(nextArg)

  /** All parameters of components of pre, indexed by type. */
  //private val allPreParams: Array[List[Identity]] = 
  //  Remapper.makeOtherArgMap(pre.paramsBitMap)

  import Unification.UnificationList // = List[(Int,Int)]

  /** Representation of a linkage.  A pair (i, j) represents a linkage between
    * cpts(i) and preCpts(j). */
  private type Linkage = (Int,Int)

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
            // reference.
            var refJs = pre.refsIndexMap(t)(id1) 
            if(refJs.nonEmpty){
              // Index of component in cv with identity (t,id), or -1 if no such.
              val i = cv.idsIndexMap(t)(id)
              // If not unified, we have a linkage i->j for j in refJs
              if(i >= 0 && !cvUnifs(i)){
                while(refJs.nonEmpty && result == null){
                  val j = refJs.head; refJs = refJs.tail
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
    * map under rdMap to a missing reference of pre.principal. */
  private def findLinkagesC(unifs: UnificationList, rdMap: RemappingMap)
      : ArrayBuffer[Parameter] = {
    val result = new ArrayBuffer[Parameter]
    // Linkages for condition (c).  Iterate through the parameters of
    // cv.principal.
    val cvPrincParams = cv.principal.processIdentities; var i = 1
    while(i <  cvPrincParams.length){
      val (t,id) = cvPrincParams(i); i += 1
      if(!isDistinguished(id) && !cptIds(t)(id)){
        val id1 = rdMap(t)(id)
        // Are id and id1 missing parameters for cv, pre, respectively?
        if(id1 >= 0 && preCpts(0).processIdentities.contains((t,id1)) &&
            !preCptIds(t)(id1))
          result += ((t,id))
      }
    }

    result
    // IMPROVE: use bitmaps for parameters
  }

  /** Extend map to map all undefined values to distinct fresh values. */
  @inline private def mapUndefinedToFresh(map: RemappingMap) = {
    for(t <- 0 until numTypes){
      var next = nextArg(t)
      for(i <- 0 until map(t).length)
        if(map(t)(i) < 0){ map(t)(i) = next; next += 1 }
    }
  }

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
    // if(highlight) println("otherArgs = "+otherArgs.mkString("; "))
    //println("extendForLinkage: "+otherArgs.mkString("; "))
    // if(true)
    if(false) extendMapOverComponent(rdMap, c1, otherArgs)
    else{
      // For each non-distinguished parameter (t,x) of c1, the values (t,y)
      // that (t,x) can be mapped to: elements of otherArgs(t) such that for
      // each (ii,jj) in doneB, if (t,x) is a parameter of cv.cpts(ii), then
      // (t,y) is not a parameter of preCpts(jj); and not mapping an identity
      // to an identity.  Indexed following the indices of parameters in c1.
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
    // Note: the latter gives ~14% fewer maps for lazySet with bound 48. 

    // assert(oldRes.length >= newRes.length, 
    //   s"oldRes = "+oldRes.map(Remapper.show).mkString("\n  ")+
    //     "\nnewRes = "+newRes.map(Remapper.show).mkString("\n  ")+
    //     s"\ndoneB = $doneB; c1 = $c1; c2 = $c2; "+
    //     "\n cpts = "+StateArray.show(cpts)+
    //     "\npreCpts = "+StateArray.show(preCpts))
    // newRes
  }

  /** Extend map over the parameters of c in all possible ways, mapping the
    * parameter with index ix to an element of candidates(ix), or not.  map is
    * mutated, but all updates are rolled back. */
  private def extendMapByIndex(
    map: RemappingMap, c: State, candidates: Array[List[Identity]])
      : ArrayBuffer[RemappingMap] = {
    val result = new ArrayBuffer[RemappingMap] // builds result
    val addedParams = Pools.getBitMap // newBitMap  // Parameters that we have added to map

    /* Extend map over parameters of c from index ix onwards. */
    def rec(ix: Int): Unit = {
      if(ix == c.length){ 
        /*assert(Remapper.isInjective(map));*/ result += Remapper.cloneMap(map)
      }
      else{
        val(t,x) = c.processIdentity(ix)
        if(!isDistinguished(x) && map(t)(x) < 0){
          // Try mapping x to each element of candidates(ix)
          // for(y <- candidates(ix); if !addedParams(t)(y)){
          var cands = candidates(ix)
          while(cands.nonEmpty){
            val y = cands.head; cands = cands.tail
            if(!addedParams(t)(y)){
              //assert(!map(t).contains(y))
              //assert(!(cptIds(t)(x) && preCptIds(t)(y)))
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


  /** Find all consistent extensions of map over the parameters of c, mapping
    * each parameter to an element of otherArgs, or not. */
  def extendMapOverComponent(map: RemappingMap, c: State, otherArgs: OtherArgMap)
      : ArrayBuffer[RemappingMap] = {
    val extendedMaps = new ArrayBuffer[RemappingMap]
    extendMapOverComponent1(map, c, otherArgs, extendedMaps)
    extendedMaps
  }

  /** Find all consistent extensions of map over the parameters of c, mapping
    * each parameter to an element of otherArgs, or not.  Add all such to
    * result. */
  private def extendMapOverComponent1(
    map: RemappingMap, c: State, otherArgs: OtherArgMap, 
    result: ArrayBuffer[RemappingMap]) 
  = {
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
    rec(0)
  }

  /** Implementation of allExtensions from the paper.  All extensions of rdMap,
    * mapping undefined parameters to an arbitrary parameter of pre, or the
    * next fresh parameter, but not to parameters of resultRelevantParams, and
    * only consistently with doneB.  Add each to extensions. */
  private def allExtensions(
    resultRelevantParams: BitMap, rdMap: RemappingMap, 
    doneB: List[Linkage], extensions: ArrayBuffer[RemappingMap])
  = {
    // All parameters that each parameter can be mapped to
    val candidates = getCandidatesMap(resultRelevantParams, rdMap, doneB)
    // Build all extensions of rdMap, mapping each parameter to each element
    // of candidates(x), or not, injectively.
    val eMaps = extendMapToCandidates(rdMap, candidates)
    // Map remainder to fresh variables, and add to extensions.
    var i = 0
    while(i < eMaps.length){
      val eMap = eMaps(i); i += 1
      mapUndefinedToFresh(eMap); extensions += eMap 
      Profiler.count("allExtensions - add")
    }
  }

  /** Extend rdMap, mapping each parameter (t,p) to each element of
    * candidates(t)(p), or not.  rdMap is mutated, but all changes are
    * backtracked. */
  private def extendMapToCandidates(
    rdMap: RemappingMap, candidates: Array[Array[List[Identity]]]) 
      : ArrayBuffer[RemappingMap] = {
    val result = new ArrayBuffer[RemappingMap]
    // bitmap showing which parameters of pre have been used in the current
    // mapping.  Calls to rec mutate this but backtrack the updates.
    val used = Array.tabulate(numTypes)(t => 
      new Array[Boolean](preParamSizes(t)))

    /* Remap from (t,i) onwards. */
    def rec(t: Type, i: Identity): Unit = {
      if(t == numTypes) result += Remapper.cloneMap(rdMap)
      else if(i == rdMap(t).length) rec(t+1,0)
      else{
        if(candidates(t)(i).nonEmpty){
          assert(rdMap(t)(i) < 0)
          for(x <- candidates(t)(i); if !used(t)(x)){
            used(t)(x) = true             // temporary update (*)
            rdMap(t)(i) = x; rec(t,i+1)
            used(t)(x) = false            // backtrack (*)
          }
          rdMap(t)(i) = -1 // undo update
        }
        rec(t,i+1) // leave (t,i) unmapped
      }
    }

    rec(0,0); result
  }

  /** Build map showing what each parameter of cv can be mapped to so as to be
    * consistent with rdMap (so giving List() on parameters in dom rdMap, and
    * not mapping to an element of range rdMap) and resultRelevantParams (not
    * mapping to any such parameter) and respecting doneB (for each (i,j) in
    * doneB, not mapping any parameter of cv.cpts(i) to a component of
    * pre.cpts(j)).  */
  private def getCandidatesMap(
    resultRelevantParams: BitMap, rdMap: RemappingMap, doneB: List[Linkage])
      : Array[Array[List[Identity]]] = {
    // All params of pre, except those in resultRelevantParams or range rdMap 
// IMPROVE: memoise at least some of this
    val otherArgs: Array[List[Identity]] = Array.tabulate(numTypes)(t => 
      pre.getAllParams(t).filter(p => 
        !resultRelevantParams(t)(p) && !rdMap(t).contains(p)))
    // The same but excluding identities
    val nonIds = Array.tabulate(numTypes)(t => 
      otherArgs(t).filter(p1 => !preCptIds(t)(p1)))
    // List of parameters that each parameter x of cv could be mapped to;
    // empty list if x is already mapped in rdMap; otherwise relevant members
    // of otherArgs, not mapping an identity to an identity.
    val candidates = Array.tabulate(numTypes)(t => 
      Array.tabulate(rdMap(t).length)(p => 
        if(rdMap(t)(p) < 0) 
          if(cptIds(t)(p)) nonIds(t) // otherArgs(t).filter(p1 => !preCptIds(t)(p1))
          else otherArgs(t)
        else List() 
      ))
    // For each (i,j) in doneB, for each param (t,x) of cv.cpts(i),
    // remove all parameters of preCts(j) from the list candidates(x). 
    for((i,j) <- doneB){
      val preC = preCpts(j)
      for((t,x) <- cpts(i).processIdentities; if !isDistinguished(x)){
        candidates(t)(x) = candidates(t)(x).filter(y => !preC.hasParam(t,y))
      }
    }
    candidates
  }

  /** Implementation of makeExtensions from the paper.  Create all required
    * extensions of result-defining map rdMap.  Note: rdMap may be mutated. */
  def makeExtensions(
    unifs: UnificationList, resultRelevantParams: BitMap, rdMap: RemappingMap, 
    isPrimary: Boolean)
      : ArrayBuffer[RemappingMap] = {
    val extensions = new ArrayBuffer[RemappingMap] 
    makeExtensions1(
      unifs, resultRelevantParams, rdMap, List(), isPrimary, extensions)
    extensions
  }

  /** Implementation of makeExtensions from the paper.  Create all required
    * extensions of result-defiling map rdMap.  Add all such to extensions.
    * doneB gives the instances of condition (b) that we have dealt with so
    * far.  Note: rdMap may be mutated. */
  private def makeExtensions1(
    unifs: UnificationList, resultRelevantParams: BitMap, 
    rdMap: RemappingMap, doneB: List[Linkage], 
    isPrimary: Boolean, extensions: ArrayBuffer[RemappingMap])
      : Unit = {
    // if(highlight)println("makeExtensions1; rdMap = "+Remapper.show(rdMap)+
    //   s"; doneB = $doneB")
    val linkagesC = findLinkagesC(unifs, rdMap)
    if(linkagesC.nonEmpty) 
      allExtensions(resultRelevantParams, rdMap, doneB, extensions)
    else{
      val newLinkage = findLinkage(unifs, rdMap, doneB) 
      if(newLinkage == null){ // map remaining params to fresh
        mapUndefinedToFresh(rdMap)
        // Add to extensions if not there already
        var ix = 0
        while(ix < extensions.length && 
            !Remapper.equivalent(extensions(ix), rdMap))
          ix += 1
        if(ix == extensions.length)
          // if(extensions.forall(m => !Remapper.equivalent(m, rdMap))){
          extensions += rdMap
          // Profiler.count("makeExtensions1 -- add")
      }
      else{
        val (i,j) = newLinkage
        // FIXME: need to respect doneB below
        val extendedMaps = 
          extendForLinkage(rdMap, resultRelevantParams, i, j, isPrimary, doneB)
        // if(highlight) 
        //   println("extendedMaps: "+extendedMaps.map(Remapper.show(_)))
        var k = 0
        while(k < extendedMaps.length){
          // Profiler.count("makeExtensions1 iter")
          val eMap = extendedMaps(k); k += 1
          // if(highlight) println("eMap = "+Remapper.show(eMap))
          makeExtensions1(unifs, resultRelevantParams, eMap, 
            (i,j)::doneB, isPrimary, extensions)
        }
      }
    }
  }
  /* Note, we remove repetitions above.  For example, with TrieberStack.csp 
   * pre = [32(N0) || 34()] || [23(T0,N0,N1) || 15(N1,N2)]
   * cv = [32(N0) || 34()] || [24(T0,N1,N2) || 11(N1,N2)]
   * and N2 -> N1, we get linkages (0,0) and (1,0), from both components of
   * cv.  Each might or might not add the mapping N1 -> N2, so there are two
   * ways to get this mapping.  It's not clear whether this is worthwhile.
   * There might still be repetitions arising within allExtensions.  */

  // ========= Hooks for testing

  private val outer = this

  /** Object providing hooks for testing. */
  object TestHooks{
    def findLinkages(unifs: UnificationList, rdMap: RemappingMap) = 
      outer.findLinkage(unifs, rdMap, List())
    // IMPROVE: use same names

    val findLinkagesC = outer.findLinkagesC _

    val getCandidatesMap = outer.getCandidatesMap _

    val extendMapToCandidates = outer.extendMapToCandidates _

    // makeExtensions is public
  }
}
