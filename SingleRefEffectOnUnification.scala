package ViewAbstraction

import ox.gavin.profiling.Profiler
import RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}

// FIXME: there's repeated code between here and EffectOnUnification

/** Get information concerning transitions induced by trans working on cv. */
class SingleRefEffectOnUnification(trans: Transition, cv: ComponentView){
  /* Relationship of main functions.
   * apply
   * |--Unification.allUnifs
   * |--isSufficientUnif
   * |--makePrimaryInduced
   * |  |--mkOtherArgsMap       
   * |  |  |--addIdsFromNewRef
   * |  |--extendToRDMap     (produces primary result-defining maps)
   * |  |--makePrimaryExtension
   * |  |  |--RemappingExtender.makeExtensions
   * |--makeSecondaryInduced
   *    |--getSecondaryInfo
   *    |--mkSecondaryOtherArgsMap
   *    |--RemappingExtender.extendMapOverComponent
   *    |--makeSecondaryExtension
   *    |  |--RemappingExtender.makeExtensions
   * 
   * IMPROVE: maybe factor out mkOtherArgsMap, extendToRDMap,
   * getSecondaryInfo, mkSecondaryOtherArgsMap.
   */

  Profiler.count("SingleRefEffectOnUnification")

  /* A few object variables, extracted directly from pre, post and cv, used in
   * several functions. */
  private val pre = trans.pre; private val post = trans.post
  private val servers = pre.servers
  require(servers == cv.servers && servers.isNormalised)

  private val preCpts = pre.components; private val postCpts = post.components
  require(preCpts.length == postCpts.length)
  private val cpts = cv.components
  // if(debugging) StateArray.checkDistinct(cpts)
  // ID of principal of cv
  private val (cvpf, cvpid) = cv.principal.componentProcessIdentity

  import Unification.UnificationList // = List[(Int,Int)]
  // Contains (i,j) if cpts(i) is unified with preCpts(j)

  // A representation of map |> post.servers
  import ServersReducedMap.ReducedMap 

  import RemappingExtender.{CandidatesMap}

  // Types of the result
  import SingleRefEffectOnUnification.{InducedInfo, SecondaryInducedInfo}

  import SingleRefEffectOnUnification.isEmpty

  /** Variables in which we build up the result. */
  private val result = new InducedInfo
  private val result2 = new SecondaryInducedInfo 

  /** The object responsible for extending result-defining mappings. */
  val remappingExtender = new RemappingExtender(trans,cv)

  /** Which secondary components can gain a reference to cv.principal?  All
    * pairs (i,p1) such that pre.components(i) changes state in the transition
    * (with (i>0), and p1 is a new parameter of post.components(i), of the
    * same type as cv.principal.id, and not matching and parameter of pre. */
  private def acquiredRefs: List[(Int,Parameter)] = trans.acquiredRefs(cvpf)

  val highlight = 
    Transition.highlight(trans) && {
      val princ = cv.components(0); // 44(T2,N2,N3)
      princ.cs == 44 && princ.ids.sameElements(Array(1,1,2))
    } && {
      val second = cv.components(1); // 16(N2,T3,N4,N5)
      second.cs == 16 && second.ids.sameElements(Array(1,2,3,4))
    }

  def recycle(map: RemappingMap) = Pools.returnRemappingRows(map)

  // =======================================================

  /** The main function.  */
  def apply(): (InducedInfo, SecondaryInducedInfo) = {
    if(highlight) println(s"SREOU.apply($trans,\n  $cv)")
    val allUnifs = Unification.allUnifs(pre, cv); var k = 0
    while(k < allUnifs.length){
      val (map1,unifs) = allUnifs(k); k += 1
      // if(highlight && map1(0)(3) == 2) 
      //   println(s"map1 = "+Remapper.show(map1)+s"; unifs = $unifs")
      if(isSufficientUnif(unifs)) makePrimaryInduced(map1, unifs)
      if(!isFullUnif(unifs)) makeSecondaryInduced(map1, unifs)
      recycle(map1)
    } // end of while loop iterating over unifs
    (result,result2)
  }

  /** Does this represent a unification of all components? */
  @inline private def isFullUnif(unifs: UnificationList) =
    unifs.length == cpts.length && unifs.contains((0,0))

  /** Try to create primary induced transitions based on map1 and unifs. */
  @inline private 
  def makePrimaryInduced(map1: RemappingMap, unifs: UnificationList) = {
    val postServers = post.servers
    // Result-relevant parameters: parameters to map params of cv to, in order
    // to create result-defining map.
    val otherArgsBitMap = mkOtherArgsMap(map1, unifs)
    // if(highlight) println("otherArgsBitMap = "+
    //   otherArgsBitMap.map(_.mkString("<", ", ", ">")).mkString("; "))
    // Primary result-defining maps
    val rdMaps =
      // If there are no new parameters, then the only result-defining map is
      // map1. 
      if(isEmpty(otherArgsBitMap)){
        // If no unified component changes state and the servers do not get
        // any new reference (which includes the case that unifs is empty),
        // and we've previously successfully induced a transition with this
        // change of servers, then this instance can only reproduce that
        // transition. 
        if(!trans.isChangingUnif(unifs) && !trans.serverGetsNewId &&
            cv.containsDoneInduced(postServers))
          SingleRefEffectOnUnification.EmptyArrayBuffer 
        // Note: it's necessary to clone below, because map1 gets used again
        // with secondary transitions.
        else ArrayBuffer(Remapper.cloneMap(map1))
      }
      else extendToRDMap(map1,otherArgsBitMap) // ~0.19%

    // Extend with extra linkages and fresh parameters
    var i = 0
    while(i < rdMaps.length){
      val rdMap = rdMaps(i); i += 1
      // if(highlight) println("rdMap = "+Remapper.show(rdMap))
      // post-states of unified components
      val postUnified = trans.getPostUnified(unifs, cpts.length)
      val reducedMapInfo = Remapper.reduceMap(rdMap)
      // Does this duplicate a previous transition: no unifications, no
      // acquired references, and the same result-defining map and post-states
      // of unified components?  Currently disabled, because it doesn't make
      // much difference.  IMPROVE
      val duplicated =  StoreDoneInducedPostServersRemaps && (
        if(DetectRepeatRDMapWithUnification)
          !trans.doesPrincipalAcquireRef(unifs) && 
            cv.containsDoneInducedPostServersRemaps(
              postServers, reducedMapInfo, postUnified)
        else unifs.isEmpty && // current version
          cv.containsDoneInducedPostServersRemaps(postServers, reducedMapInfo) )
      if(!duplicated)
        makePrimaryExtension(unifs, otherArgsBitMap, rdMap, reducedMapInfo)
      // Note: rdMap is included in result or recycled by above.
    }
  }

  /** Does unifs give sufficient unifications such that it might produce a new
    * view via a primary induced transition?  */
  @inline private def isSufficientUnif(unifs: UnificationList): Boolean = 
    if(unifs.length == cpts.length && unifs.contains((0,0))) false
    else trans.changedServers || trans.isChangingUnif(unifs)
    // There are various plausible-looking alternatives that don't work here.
    // For example, something like
    // unifs.nonEmpty || cv.addDoneInduced(postServers)
    // doesn't work, because the previous case might have corresponded to a
    // different set of linkages.  And
    // unifs.nonEmpty || !cv.containsDoneInduced(postServers)
    // (where there's a corresponding addDoneInduced in
    // EffectOn.recordInduced) doesn't work, because the previous case only
    // implies that *one* of the result-defining maps led to success, not all
    // of them.

  /** Create a BitMap containing all parameters: (1) in newServerIds (parameters
    * in post.servers but not pre.servers), or (2) in a unified component of
    * post.cpts; (3) in post.cpts for a component to which cv.principal gains
    * a reference.  But excluding parameters of servers or those in the range
    * of map1 in all cases.  */
  @inline private 
  def mkOtherArgsMap(map1: RemappingMap, unifs: UnificationList)
      : BitMap = {
    // (1) parameters in newServerIds
    val otherArgsBitMap = trans.getNewServerIds; var us = unifs
    while(us.nonEmpty){
      val (j, i) = us.head; us = us.tail
      // (2) Add new parameters of postCpts(i), which is unified with a
      // component of cv.
      if(trans.changedStateBitMap(i))
        postCpts(i).addIdsToBitMap(otherArgsBitMap, servers.idsBitMap)
      // (3) If this is the unification of the principal of cv, which changes
      // state and gains a reference to another component c, include the
      // parameters of c from postCpts.
      if(j == 0 && trans.changedStateBitMap(i))
        addIdsFromNewRef(otherArgsBitMap, i) 
    }
// IMPROVE: avoid adding them in the first place? 
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
    * resultRelevantParams, or not.  
    * 
    * Each map produced is fresh.  map is mutated, but changes are rolled
    * back. */
  private def extendToRDMap(map: RemappingMap, resultRelevantParams: BitMap)
      : ArrayBuffer[RemappingMap] = {
    Profiler.count("extendToRDMap")
    // IDs of components in pre, cv
    //val preCptIds = pre.cptIdsBitMap _  //val cptIdsX = cv.cptIdsBitMapX 
    val cptIds = cv.cptIdsBitMap 
    // val otherArgs = Remapper.makeOtherArgMap(resultRelevantParams)
    // Find upper bound on resultRelevantParams(t) for each t
    val bounds = new Array[Int](numTypes); var t = 0
    while(t < numTypes){
      var i = resultRelevantParams(t).length
      // Inv: resultRelvantParams(t)[i..) all false
      while(i > 0 && !resultRelevantParams(t)(i-1)) i -= 1
      bounds(t) = i; t += 1
    }
    val mapBuff = new ArrayBuffer[RemappingMap]

    /* Extend map, remapping parameters from (t,i) onwards. */
    def rec(t: Int, i: Int): Unit = {
      if(t == numTypes) mapBuff += Remapper.cloneMap(map)  // done this branch
      else if(i == map(t).length) rec(t+1, 0) // advance
      else if(map(t)(i) >= 0) rec(t, i+1) // advance
      else{
        val isId = IdentitiesBitMap(cptIds,t,i) //
        //val isIdX = cptIdsX(t)(i)  // Is this an identity?
        // assert(isId == isIdX, 
        //   s"cptIdsX = "+cptIdsX.map(_.mkString("(",",",")")).mkString("; ")+
        //   s"cptIds = $cptIds; t = $t; i = $i") 
        // map (t,i) to each element of otherArgs(t)
        var id1 = 0
        while(id1 < bounds(t)){
          if(resultRelevantParams(t)(id1)){
            // Don't map an identity to an identity
            if(!(isId && pre.cptIdsBitMap(t)(id1))){
              resultRelevantParams(t)(id1) = false
              map(t)(i) = id1            // temporary update (+)
              rec(t, i+1)
              resultRelevantParams(t)(id1) = true
              map(t)(i) = -1             // backtrack (+)
            }
          }
          id1 += 1
        }
        // Also include case of not updating this param
        rec(t, i+1)
      }
    } // end of rec

    rec(0,0); mapBuff
  }

  /* Extend the result-defining map rdMap, based on unifications unifs, to
   * produce all primary representative extensions.  For each such map, add an
   * appropriate tuple to result.  rdMap might be included in the result or
   * recycled.  */
  private def makePrimaryExtension(
    unifs: UnificationList, resultRelevantParams: BitMap, 
    rdMap: RemappingMap, reducedMapInfo: ReducedMap)
  = {
    // val hl = highlight && rdMap(0).sameElements(Array(0,-1,-1,2,3))
    // if(hl) println(s"makePrimaryExtension(unifs = $unifs, "+
    //   "rdMap = "+Remapper.show(rdMap))
    Profiler.count("makePrimaryExtension")
    val extensions = 
      remappingExtender.makeExtensions(unifs, resultRelevantParams, rdMap, true)
    // Note: recycles or returns rdMap
    for((map1, candidates) <- extensions){
      // IMPROVE
      if(debugging) assert(Remapper.isInjective(map1))
      // if(!useNewEffectOnStore) assert(map1.forall(a => a.forall(_ >= 0)))
      result += ((map1, candidates,  unifs, reducedMapInfo))
    }
  }

  // ========= Secondary induced transitions

  @inline private 
  def makeSecondaryInduced(map1: RemappingMap, unifs: UnificationList) = {
    //Secondary induced transitions; improve: test if sufficient unifs?
    val secondaryInfo = getSecondaryInfo(map1); var i = 0
    while(i < secondaryInfo.length){
      val (map2,ix) = secondaryInfo(i); i += 1; val sc = postCpts(ix)
      val otherArgsBitMap = mkSecondaryOtherArgsMap(map2, sc)
      val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
      // Secondary result-defining maps
      val rdMaps =
        remappingExtender.extendMapOverComponent(map2, cpts(0), otherArgs)
      recycle(map2)
      var j = 0
      // Then consider linkages
      while(j < rdMaps.length){
        val rdMap = rdMaps(j); j += 1
        makeSecondaryExtension(unifs, otherArgsBitMap, rdMap, ix)
      }
    } // end of while loop iterating over secondaryInfo
  }


  /* Extend the result-defining map rdMap, based on unifications unifs, to
   * produce all secondary representative extensions corresponding to
   * postCpts(ix).  For each such map, add an appropriate tuple to result2.
   * rdMap is recycled or included in the result. */
  private def makeSecondaryExtension(
    unifs: UnificationList, resultRelevantParams: BitMap, 
    rdMap: RemappingMap, ix: Int)
  = {
    if(showTransitions) println("makeSecondaryExtension: "+Remapper.show(rdMap))
    val extensions = 
      remappingExtender.makeExtensions(unifs, resultRelevantParams, rdMap, false)
    // Note: the above recycles rdMap or includes it in result
    for((map1,candidates/*rrParams,doneB*/) <- extensions){
      //assert(rrParams == resultRelevantParams)
// IMPROVE
      if(debugging) assert(Remapper.isInjective(map1))
      result2 += ((map1, candidates, /*rrParams, doneB,*/ unifs, ix))
    }
  }

  /** Get information about secondary induced transitions: pairs (map2,i) such
    * that map2 extends map1 to map cv.principal's identity to match a
    * reference of a secondary component of post, postCpts(i), and that
    * reference is used to create views. */ 
  private def getSecondaryInfo(map1: RemappingMap)
      : ArrayBuffer[(RemappingMap, Int)] = {
    //val preCptIds = pre.cptIdsBitMap
    val result = new ArrayBuffer[(RemappingMap, Int)]; var ar = acquiredRefs
    while(ar.nonEmpty){
      val (i,(t,id)) = ar.head; ar = ar.tail
      assert(t == cvpf); val id1 = map1(t)(cvpid)
      // Check extending map1 with cvpid -> id is consistent: either (1) it's
      // already there; or (2) map1 is undefined on cvpid, id isn't in the
      // range, and id isn't an identity in pre (which would imply
      // unification).
      if(id1 == id || 
          id1 < 0 && !pre.cptIdsBitMap(t)(id) && !map1(t).contains(id) ){
        val map2 = Remapper.cloneMap(map1); map2(cvpf)(cvpid) = id
        // map2 is recycled in makeSecondaryInfo
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
    val otherArgsBitMap = trans.getNewServerIds 
    // (2) parameters of sc
    sc.addIdsToBitMap(otherArgsBitMap, servers.idsBitMap) 
    // Remove parameters of range map1
    Remapper.removeFromBitMap(map1, otherArgsBitMap)
    otherArgsBitMap
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

    val isSufficientUnif = outer.isSufficientUnif _

    val acquiredRefs = outer.acquiredRefs 

    val getSecondaryInfo = outer.getSecondaryInfo _

    val extendMapOverComponent = outer.remappingExtender.extendMapOverComponent _
  } // end of TestHooks
}

// =======================================================

object SingleRefEffectOnUnification{
  /** An empty ArrayBuffer[RemappingMap], used in apply (to avoid unnecessarily
    * creating a new ArrayBuffer.  It's fine for this to be shared between
    * threads. */
  private val EmptyArrayBuffer = new ArrayBuffer[RemappingMap]()

  // A representation of map |> post.servers
  import ServersReducedMap.ReducedMap 

  import Unification.UnificationList // = List[(Int,Int)]
  // Contains (i,j) if cpts(i) is unified with preCpts(j)

  import RemappingExtender.Linkage // = (Int,Int)

  import  RemappingExtender.CandidatesMap

  import CompressedCandidatesMap.CompressedCandidatesMap

  /** The part of the result relating to primary induced transitions.  Each
    * tuple (map, resultRelevantParams, doneB, unifs, reducedMap) indicates
    * the remapping of cv.cpts by map, with resultRelevantParams and doneB as
    * in RemappingExtender, and with unifications corresponding to unifs;
    * reducedMap is the reduced version of map. */
// IMPROVE: map isn't used, other than being recycled
  type InducedInfo = 
    ArrayBuffer[(RemappingMap, CompressedCandidatesMap, UnificationList, ReducedMap)]
    //ArrayBuffer[(RemappingMap, CandidatesMap, UnificationList, ReducedMap)]

  /** The part of the result corresponding to secondary induced transitions.
    * Each tuple (map, resultRelevantParams, doneB, unifs, i) represents a
    * remapping of cv.cpts by map, with resultRelevantParams and doneB as in
    * RemappingExtender, and with unifications unifs, and that the ith
    * component of the transition gains a reference to cv.principal. */
  type SecondaryInducedInfo = 
    ArrayBuffer[(RemappingMap, CompressedCandidatesMap, UnificationList, Int)]

  /** Does otherArgs represent the empty set? */
  @inline private def isEmpty(otherArgs: BitMap) = {
    var t = 0; var empty = true
    while(t < numTypes && empty){
      var i = 0; val len = otherArgs(t).length
      while(i < len && !otherArgs(t)(i)) i += 1
      empty = i == len; t += 1
    }
    empty
  }
  // IMPROVE: this result could be calculated within makeOtherArgsMap.  But
  // this doesn't seem to be a big cost.


  /** All common included missing references from cpts1 and cpts2. */
  @inline def commonMissingRefs(cpts1: Array[State], cpts2: Array[State])
      : List[ProcessIdentity] = {
    var missingRefs1: List[ProcessIdentity] = StateArray.missingRefs(cpts1)
    val missingRefs2: List[ProcessIdentity] = StateArray.missingRefs(cpts2)
    // The common missing references
    var missingCRefs = List[ProcessIdentity]()
    while(missingRefs1.nonEmpty){
      val pid = missingRefs1.head; missingRefs1 = missingRefs1.tail
      if(contains(missingRefs2, pid)) missingCRefs ::= pid
    }
    missingCRefs
  }

}
