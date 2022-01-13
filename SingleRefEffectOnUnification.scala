package ViewAbstraction

import RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}

// FIXME: there's a lot of repeated code between here and EffectOnUnification

class SingleRefEffectOnUnification(
  pre: Concretization, post: Concretization, cv: ComponentView){

  /* Relationship of main functions.
   * apply
   * |--Unification.allUnifs
   * |--isSufficientUnif
   * |--mkOtherArgsMap       
   * |  |--addIdsFromNewRef
   * |--extendToRDMap     (produces primary result-defining maps)
   * |--extendMapping     (adds extra linkages and fresh params)
   * |  |--findLinkages
   * |  |--extendForLinkages
   * |     |--extendForLinkage
   * |  |--mapUndefinedToFresh
   * |--getSecondaryInfo
   * |--mkSecondaryOtherArgsMap
   * |--extendMapOverComponent
   */

  /* A few object variables, extracted directly from pre, post and cv, used in
   * several functions. */
  private val servers = pre.servers
  require(servers == cv.servers && servers.isNormalised)
  private val postServers = post.servers
  private val changedServers = servers != postServers

  // All params in post.servers but not in pre.servers, as a bitmap.
  private val newServerIds: Array[Array[Boolean]] = 
    ServerStates.newParamsBitMap(servers, post.servers)

  private val preCpts = pre.components; private val postCpts = post.components
  require(preCpts.length == postCpts.length)
  private val cpts = cv.components
  if(debugging) StateArray.checkDistinct(cpts)
  // ID of principal of cv
  private val (cvpf, cvpid) = cv.principal.componentProcessIdentity
  // IDs of components in pre, cv
  private val preCptIds = preCpts.map(_.componentProcessIdentity)
  private val cptIds = cpts.map(_.componentProcessIdentity)

  import Unification.UnificationList // = List[(Int,Int)]
  // Contains (i,j) if cpts(i) is unified with preCpts(j)

  // A representation of map |> post.servers
  import ComponentView.ReducedMap 

  type CombineResult1 = 
    ArrayBuffer[(RemappingMap, Array[State], UnificationList, ReducedMap)]

  /** The part of the result corresponding to secondary induced transitions.
    * The Int field is the index of the component in pre/post that gains
    * access to cv.principal. */
  type CombineResult2 = ArrayBuffer[(Array[State], UnificationList, Int)]

  /** Variables in which we build up the result. */
  private val result = new CombineResult1
  private val result2 = new CombineResult2

  /** Bit map indicating which components have changed state. */
  private val changedStateBitMap = { 
    val changedStateBitMap = new Array[Boolean](preCpts.length); var i = 0
    while(i < preCpts.length){
      changedStateBitMap(i) = preCpts(i) != postCpts(i); i += 1
    }
    changedStateBitMap
  }

  /** A NextArgMap, containing values greater than anything in pre or post. */
  private val nextArg: NextArgMap = pre.getNextArgMap
  post.updateNextArgMap(nextArg)

  /** Which secondary components can gain a reference to cv.principal?  All
    * pairs (i,p1) such that pre.components(i) changes state in the transition
    * (with (i>0), and p1 is a new parameter of post.components(i), of the
    * same type as cv.principal.id, and not matching . */
  private val acquiredRefs: List[(Int,Parameter)] = { 
    var aR = List[(Int,Parameter)]()
    for(i <- 1 until preCpts.length; if preCpts(i) != postCpts(i)){
      val postParams = postCpts(i).processIdentities
      val preParams = preCpts(i).processIdentities
      for(j <- 1 until postParams.length){
        val p1 = postParams(j)
        if(p1._1 == cvpf && !preParams.contains(p1)) aR ::= (i,p1)
      }
    }
    aR
  }

  // =======================================================

  /** The main function. */
  def apply(): (CombineResult1, CombineResult2) = {
    val map0 = servers.remappingMap(cv.getParamsBound)
    val allUnifs = Unification.allUnifs(map0, preCpts, cpts)

    for((map1, unifs) <- allUnifs){
      if(isSufficientUnif(unifs)){
        // Result-relevant parameters: parameters to map params of cv to, in
        // order to create result-defining map.
        val otherArgsBitMap = mkOtherArgsMap(map1, unifs)
        //val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
        // Primary result-defining maps
        val rdMaps = extendToRDMap(map1,otherArgsBitMap)
        // Extend with extra linkages and fresh parameters
        for(rdMap <- rdMaps) extendMapping(unifs, otherArgsBitMap, rdMap, None)
      }
      // else println("Not sufficient unif "+unifs)

      //Secondary induced transitions
// IMPROVE: inside "if"?  
      val secondaryInfo = getSecondaryInfo(map1)
      for((map2, i) <- secondaryInfo){
        val sc = postCpts(i)
        val otherArgsBitMap = mkSecondaryOtherArgsMap(map2, sc)
        val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
        // Secondary result-defining maps
        val rdMaps = new ArrayBuffer[RemappingMap]
        extendMapOverComponent(map2, cpts(0), otherArgs, rdMaps)
        // Then consider linkages
        for(rdMap <- rdMaps) extendMapping(unifs, otherArgsBitMap, rdMap, Some(i))
        // No: add to result2
// FIXME: carry on here ..................................
      }
    }
    (result,result2)
  }

  /** Does unifs give sufficient unifications such that it might produce a new
    * view?  ??? Primary or secondary ???  */
  @inline private def isSufficientUnif(unifs: UnificationList)
      : Boolean = {
    // Is there a unification with a component that changes state?
    @inline def changingUnif = {
      var us = unifs; var sufficientUnif = false
      while(!sufficientUnif && us.nonEmpty){
        sufficientUnif = changedStateBitMap(us.head._2); us = us.tail
      }
      sufficientUnif
    }

    if(unifs.length == cpts.length && unifs.contains((0,0))) false
    else true
// IMPROVE:  below
      // else if(changedServers) true 
      // else changingUnif
  }

  /** Create a BitMap containing all parameters: (1) in newServerIds (parameters
    * in post.servers but not pre.servers), or (2) in a unified component of
    * post.cpts; (3) in post.cpts for a component to which cv.principal gains
    * a reference.  But excluding parameters of servers or those in the range
    * of map1 in all cases.  */
  @inline private 
  def mkOtherArgsMap(map1: RemappingMap, unifs: UnificationList)
      : BitMap = {
    // (1) parameters in newServerIds
    val otherArgsBitMap = newServerIds.map(_.clone); var us = unifs
    while(us.nonEmpty){
      val (j, i) = us.head; us = us.tail
      // (2) Add parameters of postCpts(i), which is unified with a component
      // of cv.
      postCpts(i).addIdsToBitMap(otherArgsBitMap, servers.idsBitMap) 
      // (3) If this is the unification of the principal of cv, which changes
      // state and gains a reference to another component c, include the
      // parameters of c from postCpts.
      if(j == 0 && changedStateBitMap(i)) addIdsFromNewRef(otherArgsBitMap, i)
    }
    Remapper.removeFromBitMap(map1, otherArgsBitMap)
    otherArgsBitMap
  }

  /** Add to otherArgsBitMap any parameters of a component c to which preCpts(i)
    * gains a reference as the result of the transition. */ 
  @inline private 
  def addIdsFromNewRef(otherArgsBitMap: Array[Array[Boolean]], i: Int) = {
    val prePids = preCpts(i).processIdentities
    val postPids = postCpts(i).processIdentities
    val serverIds = servers.idsBitMap
    // Find which parameters are gained
    for(k <- 1 until postPids.length){
      val pid = postPids(k)
      if(!isDistinguished(pid._2) && !prePids.contains(pid)){
        val c = StateArray.find(pid, postCpts)
        if(c != null) c.addIdsToBitMap(otherArgsBitMap, serverIds)
      }
    }
  }

  /** Extend map, mapping undefined parameters to parameters in
    * resultRelevantParams, or not. */
  private def extendToRDMap(map: RemappingMap, resultRelevantParams: BitMap)
      : ArrayBuffer[RemappingMap] = {
    val otherArgs = Remapper.makeOtherArgMap(resultRelevantParams)
    val result = new ArrayBuffer[RemappingMap]

    /* Extend map, remapping parameters from (t,i) onwards. */
    def rec(t: Int, i: Int): Unit = {
      if(t == numTypes) result += Remapper.cloneMap(map)  // done this branch
      else if(i == map(t).length) rec(t+1, 0) // advance
      else if(map(t)(i) >= 0) rec(t, i+1) // advance
      else{
        val isId = cptIds.contains((t,i)) // Is this an identity?
        // map (t,i) to each element of otherArgs(t)
        var toDoIds = otherArgs(t); var doneIds = List[Identity]()
        // Inv: reverse(doneIds) ++ toDoIds = otherArgs(t)
        while(toDoIds.nonEmpty){
          val id1 = toDoIds.head; toDoIds = toDoIds.tail
          // Don't map an identity to an identity
          if(!(isId && preCptIds.contains((t,id1)))){
            otherArgs(t) = append1(doneIds, toDoIds) // temporary update (*)
            map(t)(i) = id1  // temporary update (+)
            rec(t, i+1)
            map(t)(i) = -1   // backtrack (+)
          }
          doneIds ::= id1 // order doesn't matter
        } // end of while loop
        otherArgs(t) = doneIds // undo (*)
        // Also include case of not updating this param
        rec(t, i+1)
      }
    } // end of rec

    rec(0,0); result
  }


  /** Representation of a linkage.  A tuple (i, j) represents a linkage
    * between cpts(i) and preCpts(j). */
  private type Linkage = (Int,Int)

  /** Find all the linkages for part (b) implied by rdMap.  All tuples (i, j,
    * id1) such that id is a parameter of cpts(i), id1 = rdMap(id) is a
    * parameter of preCpts(j), with one of those being the identity; and such
    * this doesn't represent a unification of components (with identities
    * id/id1). */
// IMPROVE: I don't think we use the identity.  
  private def findLinkages(unifs: UnificationList, rdMap: RemappingMap)
      : ArrayBuffer[Linkage] = {
    // indices of unified cpts in cv, resp, pre
    val cvUnifs = unifs.map(_._1); val preUnifs = unifs.map(_._2)
    val result = new ArrayBuffer[Linkage]

    // Iterate through rdMap
    for(t <- 0 until numTypes; id <- 0 until rdMap(t).length){
      val id1 = rdMap(t)(id)
      if(id1 >= 0){
        // Set idJ to j such that id1 is the identity of preCpts(j), or -1 if
        // no such; set refJs to all j such that id1 is a reference of
        // preCpts(j); and in each case preCpts(j) is not a unified component.
        var idJ = -1; var refJs = List[Int]()
        for(j <- 0 until preCpts.length; if !preUnifs.contains(j))
          if(preCpts(j).hasPID(t,id1)){ assert(idJ < 0); idJ = j }
          else if(preCpts(j).processIdentities.contains((t,id1))) refJs ::= j
        if(idJ >= 0){  
          // Find all i such that id is a reference of cpts(i), not unified
          for(i <- 0 until cpts.length)
            if(!cvUnifs.contains(i) && cpts(i).hasRef(t,id))
              result += ((i, idJ))
        }
        if(refJs.nonEmpty)
          // Find i with identity id and not unified, if any
          for(i <- 0 until cpts.length)
            if(cpts(i).hasPID(t,id) && !cvUnifs.contains(i))
              for(j <- refJs) result += ((i, j))
      }
    }
    result
    // IMPROVE: use bitmaps for parameters
  }

// IMPROVE: below isn't what we want.
  /** Linkages for condition (c). */
  private def findLinkagesC(unifs: UnificationList, rdMap: RemappingMap)
      : ArrayBuffer[Linkage] = {
    val result = new ArrayBuffer[Linkage]
    // Linkages for condition (c).  Iterate through the parameters of
    // cv.principal.
    val cvPrincParams = cv.principal.processIdentities
    for(i <- 1 until cvPrincParams.length){
      val (t,id) = cvPrincParams(i)
      if(!isDistinguished(id)){
        val id1 = rdMap(t)(id)
        // Are id and id1 missing parameters for cv, pre, respectively?
        if(id1 >= 0 && preCpts(0).processIdentities.contains((t,id1)) &&
            !cptIds.contains((t,id)) && !preCptIds.contains((t,id1))){
          // println(s"Missing $id -> $id1")
          result += ((0, 0))
        }
      }
    }

    result
    // IMPROVE: use bitmaps for parameters
  }

  /** Given a result-defining map rdMap that creates a linkage between c1 =
    * cpts(i) and c2 = preCpts(j), find all extensions that maps each
    * parameter of c1 to a parameter of c2, or not; but avoiding mapping to
    * elements of resultRelevantParams.  Add each to result. */
  private def extendForLinkage(
    rdMap: RemappingMap, resultRelevantParams: BitMap, 
    i: Int, j: Int, result: ArrayBuffer[RemappingMap])
  = {
    val c2 = preCpts(j); val c2Params = c2.processIdentities
    // Create otherArgMap containing all params of c2 not in range rdMap
    val otherArgs = Remapper.newOtherArgMap
    for(ix <- 0 until c2.length){
      val (t,id) = c2Params(ix)
      if(!resultRelevantParams(t)(i) && !rdMap(t).contains(id) && 
          !otherArgs(t).contains(id))
        otherArgs(t) ::= id
    }
    //println("extendForLinkage: "+otherArgs.mkString("; "))
    extendMapOverComponent(rdMap, cpts(i), otherArgs, result)
  }

  /** Find all consistent extensions of map over the parameters of c, mapping
    * each parameter to an element of otherArgs, or not.  Add all such to
    * result. */
  private def extendMapOverComponent(
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
          val isId = cptIds.contains((t,id0)) // Is this an identity?
          // map (t,id0) to each element of otherArgs(t)
          var toDoIds = otherArgs(t); var doneIds = List[Identity]()
          // Inv: reverse(doneIds) ++ toDoIds = otherArgs(t)
          while(toDoIds.nonEmpty){
            val id1 = toDoIds.head; toDoIds = toDoIds.tail
            // Don't map an identity to an identity
            if(!(isId && preCptIds.contains((t,id1)))){
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

  /** Extend rdMap corresponding to all linkages in linkages.  Note: this might
    * create new linkages.  Avoid mapping parameters to elements of
    * resultRelevantParams. */
  private def extendForLinkages(
    rdMap: RemappingMap, resultRelevantParams: BitMap,
    linkages: ArrayBuffer[Linkage])
      : ArrayBuffer[RemappingMap] = {
    assert(linkages.length <= 1) // FIXME
    // We iterate through linkages.  current represents the maps produced on
    // the previous round.
    var current = new ArrayBuffer[RemappingMap]; current += rdMap
    for(ix <- 0 until linkages.length){
      val (i, j) = linkages(ix)
      val res = new ArrayBuffer[RemappingMap]
      for(map <- current) extendForLinkage(map, resultRelevantParams, i, j, res)
      current = res
    }

    current
  }

  /** Extend the result-defining map rdMap, based on unifications unifs, to
    * produce all representative extensions, recursively mapping parameters
    * based on linkages, and then mapping other parameters to fresh
    * parameters.  If osci = None, for each such map, add an appropriate tuple
    * to result; this corresponds to a primary induced transition.  If osci =
    * Some(ix) then add an appropriate tuple to result2; this corresponds to a
    * secondary induced transition with postCpts(ix). 
    * @param resultRelevantParams a BitMap giving the result-relevant 
    * parameters, that more parameters should not be mapped to.
    * @param osci optionally the index in postCpts for which this represents a
    * secondary induced transition. */
  private def extendMapping(
    unifs: UnificationList, resultRelevantParams: BitMap, 
    rdMap: RemappingMap, osci: Option[Int])
  = {
    val linkagesB = findLinkages(unifs, rdMap)
    val linkagesC = findLinkagesC(unifs, rdMap)
    val extendedMaps = extendForLinkages(rdMap, resultRelevantParams, linkagesB)
    // FIXME: do something different with linkagesC
    for(map1 <- extendedMaps){
      val newLinkages = findLinkages(unifs, map1)
      // Are all linkages included in linkages?
      if(newLinkages.forall{ case (i,j) => linkagesB.contains((i,j)) }){
        // map remaining params to fresh and add to result
        mapUndefinedToFresh(map1)
        if(debugging) assert(Remapper.isInjective(map1))
        val newCpts = Remapper.applyRemapping(map1, cpts)
        if(osci == None){
          val reducedMapInfo: ReducedMap =
            if(unifs.isEmpty) Remapper.rangeRestrictTo(map1, postServers)
            else null
          result += ((map1, newCpts, unifs, reducedMapInfo))
        }
        else{ val ix = osci.get; result2 += ((newCpts, unifs, ix)) }
      }
      else{
        println(s"pre = $pre;\n cv = $cv;\n unifs = $unifs; rdMap = "+
          Remapper.show(rdMap)+s"; linkagesB = $linkagesB; map1 = "+
          Remapper.show(map1))
        sys.exit
// FIXME: recurse based on linkages in newLinkages not represented in linkages.
      }
    }
  }

  /** Implementation of makeExtensions from the paper.  Add all such to
    * extensions.  Note: rdMap may be mutated. */
  private def makeExtensions(
    unifs: UnificationList, resultRelevantParams: BitMap, 
    rdMap: RemappingMap, doneB: List[(Int,Int)], 
    extensions: ArrayBuffer[RemappingMap])
      : Unit = {
    val linkagesC = findLinkagesC(unifs, rdMap)
    if(linkagesC.nonEmpty) ???
    else{
      val linkagesB = findLinkages(unifs, rdMap)
      // IMPROVE: pass doneB to linkagesB
      val newLinkages = 
        linkagesB.filter( pair => !doneB.contains(pair) ).distinct
      //println("makeExtensions: "+newLinkages)
      if(newLinkages.isEmpty){ // map remaining params to fresh
        mapUndefinedToFresh(rdMap); extensions += rdMap
      }
      else{
        val (i,j) = newLinkages.head
        // FIXME: need to respect doneB below
        val extendedMaps = new ArrayBuffer[RemappingMap]
        extendForLinkage(rdMap, resultRelevantParams, i, j, extendedMaps)
        for(eMap <- extendedMaps) 
          makeExtensions(unifs, resultRelevantParams, eMap, 
            (i,j)::doneB, extensions)
      }
    }

  }

  /** Extend map to map all undefined values to distinct fresh values. */
  @inline private def mapUndefinedToFresh(map: RemappingMap) = {
    for(t <- 0 until numTypes){
      var next = nextArg(t)
      for(i <- 0 until map(t).length)
        if(map(t)(i) < 0){ map(t)(i) = next; next += 1 }
    }
  }

  // ========= Secondary induced transitions

  /** Get information about secondary induced transitions: pairs (map2,i) such
    * that map2 extends map1 to map cv.principal's identity to match a
    * reference of a secondary component of post, postCpts(i). */ 
  private def getSecondaryInfo(map1: RemappingMap)
      : ArrayBuffer[(RemappingMap, Int)] = {
    val result = new ArrayBuffer[(RemappingMap, Int)]
    for((i,(t,id)) <- acquiredRefs){
      assert(t == cvpf); val id1 = map1(t)(cvpid)
      // Check extending map1 with cvpid -> id is consistent: either (1) it's
      // already there; or (2) map1 is undefined on cvpid, id isn't in the
      // range, and id isn't an identity in pre (which would imply
      // unification).
      if(id1 == id ||
          id1 < 0 && !preCptIds.contains((t,id)) && !map1(t).contains(id) ){
        val map2 = Remapper.cloneMap(map1); map2(cvpf)(cvpid) = id
        result += ((map2, i))
      }
    }
    result
  }

  /** Make an OtherArgsMap for a secondary induced transition based on sc: (1)
    * parameters in newServerIds (parameters in post.servers but not
    * pre.servers), or (2) parameters of sc; but excluding parameters in the
    * range of map1. */
  @inline private def mkSecondaryOtherArgsMap(map1: RemappingMap, sc: State)
  : BitMap = {
    // (1) parameters in newServerIds
    val otherArgsBitMap = newServerIds.map(_.clone)
    // (2) parameters of sc
    sc.addIdsToBitMap(otherArgsBitMap, servers.idsBitMap) 
    // Remove parameters of range map1
    Remapper.removeFromBitMap(map1, otherArgsBitMap)
    otherArgsBitMap
    // Remapper.makeOtherArgMap(otherArgsBitMap)
  }

  // ========= Hooks for testing

  private val outer = this

  /** Object providing hooks for testing. */
  object TestHooks{
    /** The result-relevant parameters corresponding to map and unifs, as an
      * OtherArgMap and a bit map. */
    def mkOtherArgs(map1: RemappingMap, unifs: UnificationList)
        : (OtherArgMap, BitMap) = {
      val bitMap = mkOtherArgsMap(map1, unifs)
      (Remapper.makeOtherArgMap(bitMap), bitMap)
    }
    // Note: the tests assume an OtherArgMap, not a BitMap

    /** The secondary result-relevant parameters corresponding to map and sc, as
      * an OtherArgMap and a bit map. */ 
    def mkSecondaryOtherArgsMap(map1: RemappingMap, sc: State)
        : (OtherArgMap, BitMap) = {
      val bitMap = outer.mkSecondaryOtherArgsMap(map1, sc)
      (Remapper.makeOtherArgMap(bitMap), bitMap)
    }

    val extendToRDMap = outer.extendToRDMap _

    val findLinkages = outer.findLinkages _

    val findLinkagesC = outer.findLinkagesC _

    val extendForLinkages = outer.extendForLinkages _

    val isSufficientUnif = outer.isSufficientUnif _

    /** Extend the result-defining map rdMap, based on unifications unifs, to
      * produce all representative extensions, recursively mapping parameters
      * based on linkages, and then mapping other parameters to fresh
      * parameters. Return all resulting maps. */
    def extendPrimaryMapping(
      unifs: UnificationList, otherArgs: BitMap, rdMap: RemappingMap)
        : ArrayBuffer[RemappingMap] = {
      result.clear
      outer.extendMapping(unifs, otherArgs, rdMap, None)
      val res = result.map(_._1); result.clear; res
    }

    def extendSecondaryMapping(
      unifs: UnificationList, otherArgs: BitMap, 
      rdMap: RemappingMap, i: Int)
        : ArrayBuffer[Array[State]] = {
      result2.clear
      outer.extendMapping(unifs, otherArgs, rdMap, Some(i))
      val res = result2.map(_._1); result2.clear; res
    }

    val acquiredRefs = outer.acquiredRefs 

    val getSecondaryInfo = outer.getSecondaryInfo _

    val extendMapOverComponent = outer.extendMapOverComponent _

    def makeExtensions(unifs: UnificationList, resultRelevantParams: BitMap, 
      rdMap: RemappingMap)
        : ArrayBuffer[RemappingMap] = {
      val result = new ArrayBuffer[RemappingMap]
      outer.makeExtensions(unifs, resultRelevantParams, rdMap, List(), result)
      result
    }

  } // end of TestHooks
}
