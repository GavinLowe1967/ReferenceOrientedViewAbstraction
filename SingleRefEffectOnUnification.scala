package ViewAbstraction

import ox.gavin.profiling.Profiler
import RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}

// FIXME: there's a lot of repeated code between here and EffectOnUnification

class SingleRefEffectOnUnification(trans: Transition, cv: ComponentView){

  /* Relationship of main functions.
   * apply
   * |--Unification.allUnifs
   * |--isSufficientUnif
   * |--mkOtherArgsMap       
   * |  |--addIdsFromNewRef
   * |--extendToRDMap     (produces primary result-defining maps)
   * |--makePrimaryExtension
   * |  |--RemappingExtender.makeExtensions
   * |--getSecondaryInfo
   * |--mkSecondaryOtherArgsMap
   * |--RemappingExtender.extendMapOverComponent
   * |--makeSecondaryExtension
   * |  |--RemappingExtender.makeExtensions
   * 
   * IMPROVE: maybe factor out mkOtherArgsMap, extendToRDMap,
   * getSecondaryInfo, mkSecondaryOtherArgsMap.
   */

  /* A few object variables, extracted directly from pre, post and cv, used in
   * several functions. */
  private val pre = trans.pre; private val post = trans.post
  private val servers = pre.servers
  require(servers == cv.servers && servers.isNormalised)
  private val postServers = post.servers

  private val preCpts = pre.components; private val postCpts = post.components
  require(preCpts.length == postCpts.length)
  private val cpts = cv.components
  // if(debugging) StateArray.checkDistinct(cpts)
  // ID of principal of cv
  private val (cvpf, cvpid) = cv.principal.componentProcessIdentity
  // IDs of components in pre, cv
  private val preCptIds = pre.cptIdsBitMap 
  private val cptIds = cv.cptIds 

  import Unification.UnificationList // = List[(Int,Int)]
  // Contains (i,j) if cpts(i) is unified with preCpts(j)

  // A representation of map |> post.servers
  import ServersReducedMap.ReducedMap 

  type CombineResult1 = 
    ArrayBuffer[(RemappingMap, Array[State], UnificationList, ReducedMap)]

  /** The part of the result corresponding to secondary induced transitions.
    * The Int field is the index of the component in pre/post that gains
    * access to cv.principal. */
  type CombineResult2 = ArrayBuffer[(Array[State], UnificationList, Int)]

  /** Variables in which we build up the result. */
  private val result = new CombineResult1
  private val result2 = new CombineResult2

  /** The object responsible for extending result-defining mappings. */
  val remappingExtender = new RemappingExtender(trans,cv)

  /** Bit map indicating which components have changed state. */
  private val changedStateBitMap = trans.changedStateBitMap

  /** Which secondary components can gain a reference to cv.principal?  All
    * pairs (i,p1) such that pre.components(i) changes state in the transition
    * (with (i>0), and p1 is a new parameter of post.components(i), of the
    * same type as cv.principal.id, and not matching and parameter of pre. */
  private val acquiredRefs: List[(Int,Parameter)] = trans.acquiredRefs(cvpf)

  // =======================================================

  /** The main function. */
  def apply(): (CombineResult1, CombineResult2) = {
    // val map0 = cv.getRemappingMap // 
    //Profiler.count("SREOU.apply")
    // Early bail-out if servers don't change, no chance of unification with
    // components that change state, and no chance of secondary induced
    // transitions.  This captures over 50% of cases with lazySetNoDel.csp
    if(false && !trans.mightGiveSufficientUnifs(cpts)) (result,result2)
    else{
      val map0 = servers.remappingMap1(cv.getParamsBound)
      val allUnifs = Unification.allUnifs(map0, preCpts, cpts)
      var k = 0

      while(k < allUnifs.length){
        val (map1,unifs) = allUnifs(k); k += 1
        if(isSufficientUnif(unifs)){
          // Result-relevant parameters: parameters to map params of cv to, in
          // order to create result-defining map.
          val otherArgsBitMap = mkOtherArgsMap(map1, unifs)
          //Profiler.count("SREOU.apply-iter")

          // Primary result-defining maps
          val rdMaps =
            // If there are no new parameters, then the only result-defining
            // map is map1.  Note: it's necessary to clone below, because map1
            // gets used again with secondary transitions.  With lazySet,
            // bound 44, ~99.8% of iterations fall into this case.
// In this case, can we use the cv.containsDoneInduced technique from
// isSufficientUnifs?
            if(isEmpty(otherArgsBitMap)){
              //Profiler.count("SREOU: empty otherArgs")
              ArrayBuffer(Remapper.cloneMap(map1))
            }
            else extendToRDMap(map1,otherArgsBitMap)

          // Extend with extra linkages and fresh parameters
          var i = 0
          while(i < rdMaps.length){
            val rdMap = rdMaps(i); i += 1
            // post-states of unified components
            val postUnified = trans.getPostUnified(unifs, cpts.length)
            val reducedMapInfo = Remapper.reduceMap(rdMap)
            // Does this duplicate a previous transition: no unifications, no
            // acquired references, and the same result-defining map and
            // post-states of unified components?
            val duplicated = if(DetectRepeatRDMapWithUnification)
              !trans.doesPrincipalAcquireRef(unifs) && {
                val done = cv.containsDoneInducedPostServersRemaps(
                  postServers, reducedMapInfo, postUnified)
                // Profiler.count("containsDoneInducedPSR"+done+unifs.isEmpty);
                // lazySet bound 44: TT: 2.3B; TF: 40M; FT:9.9M; FF: 2.9M
                done }
            else unifs.isEmpty && // old version; this might be better
            cv.containsDoneInducedPostServersRemaps(postServers, reducedMapInfo)
            if(!duplicated)
              makePrimaryExtension(unifs, otherArgsBitMap, rdMap, reducedMapInfo)
          }
        } // end of if(isSufficientUnifs(unifs))

        //Secondary induced transitions; improve: test if sufficient unifs?
        val secondaryInfo = getSecondaryInfo(map1); var i = 0
        while(i < secondaryInfo.length){
          val (map2,ix) = secondaryInfo(i); i += 1
          val sc = postCpts(ix)
          val otherArgsBitMap = mkSecondaryOtherArgsMap(map2, sc)
          val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
          // Secondary result-defining maps
          val rdMaps =
            remappingExtender.extendMapOverComponent(map2, cpts(0), otherArgs)
          var j = 0
          // Then consider linkages
          while(j < rdMaps.length){
            val rdMap = rdMaps(j); j += 1
            makeSecondaryExtension(unifs, otherArgsBitMap, rdMap, ix)
          }
        }
      }
      (result,result2)
    }
  }

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
      if(changedStateBitMap(i))
        postCpts(i).addIdsToBitMap(otherArgsBitMap, servers.idsBitMap)
      // (3) If this is the unification of the principal of cv, which changes
      // state and gains a reference to another component c, include the
      // parameters of c from postCpts.
      if(j == 0 && changedStateBitMap(i)) addIdsFromNewRef(otherArgsBitMap, i)
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
    * resultRelevantParams, or not. */
  private def extendToRDMap(map: RemappingMap, resultRelevantParams: BitMap)
      : ArrayBuffer[RemappingMap] = {
    Profiler.count("extendToRDMap")
    // val otherArgs = Remapper.makeOtherArgMap(resultRelevantParams)
    // Find upper bound on resultRelevantParams(t) for each t
    val bounds = new Array[Int](numTypes); var t = 0
    while(t < numTypes){
      var i = resultRelevantParams(t).length
      // Inv: resultRelvantParams(t)[i..) all false
      while(i > 0 && !resultRelevantParams(t)(i-1)) i -= 1
      bounds(t) = i; t += 1
    }
    val result = new ArrayBuffer[RemappingMap]

    /* Extend map, remapping parameters from (t,i) onwards. */
    def rec(t: Int, i: Int): Unit = {
      if(t == numTypes) result += Remapper.cloneMap(map)  // done this branch
      else if(i == map(t).length) rec(t+1, 0) // advance
      else if(map(t)(i) >= 0) rec(t, i+1) // advance
      else{
        val isId = cptIds.contains((t,i)) // Is this an identity?
        // map (t,i) to each element of otherArgs(t)
        var id1 = 0
        while(id1 < bounds(t)){ // resultRelevantParams(t).length){ // IMPROVE bound?
          if(resultRelevantParams(t)(id1)){
            // Don't map an identity to an identity
            if(!(isId && preCptIds(t)(id1))){
              resultRelevantParams(t)(id1) = false
              map(t)(i) = id1            // temporary update (+)
              rec(t, i+1)
              resultRelevantParams(t)(id1) = true
              map(t)(i) = -1             // backtrack (+)
            }
          }
          id1 += 1
        }
/*
        var toDoIds = otherArgs(t); var doneIds = List[Identity]()
        // Inv: reverse(doneIds) ++ toDoIds = otherArgs(t)
        while(toDoIds.nonEmpty){
          val id1 = toDoIds.head; toDoIds = toDoIds.tail
          // Don't map an identity to an identity
          if(!(isId && preCptIds(t)(id1) /*.contains((t,id1))*/)){
            otherArgs(t) = append1(doneIds, toDoIds) // temporary update (*)
            map(t)(i) = id1  // temporary update (+)
            rec(t, i+1)
            map(t)(i) = -1   // backtrack (+)
          }
          doneIds ::= id1 // order doesn't matter
        } // end of while loop
        otherArgs(t) = doneIds // undo (*)
 */
        // Also include case of not updating this param
        rec(t, i+1)
      }
    } // end of rec

    rec(0,0); result
  }

  /* Extend the result-defining map rdMap, based on unifications unifs, to
   * produce all primary representative extensions.  For each such map, add an
   * appropriate tuple to result. */
  private def makePrimaryExtension(
    unifs: UnificationList, resultRelevantParams: BitMap, 
    rdMap: RemappingMap, reducedMapInfo: ReducedMap)
  = {
    val extensions = 
      remappingExtender.makeExtensions(unifs, resultRelevantParams, rdMap, true)
    for(map1 <- extensions){
      if(debugging) assert(Remapper.isInjective(map1))
      val newCpts = Remapper.applyRemapping(map1, cpts)
      result += ((map1, newCpts, unifs, reducedMapInfo))
    }
  }

  /* Extend the result-defining map rdMap, based on unifications unifs, to
   * produce all secondary representative extensions corresponding to
   * postCpts(ix).  For each such map, add an appropriate tuple to result2. */
  private def makeSecondaryExtension(
    unifs: UnificationList, resultRelevantParams: BitMap, 
    rdMap: RemappingMap, ix: Int)
  = {
    if(showTransitions) println("makeSecondaryExtension: "+Remapper.show(rdMap))
    val extensions = 
      remappingExtender.makeExtensions(unifs, resultRelevantParams, rdMap, false)
// FIXME: this seems to give repeats
    for(map1 <- extensions){
      if(debugging) assert(Remapper.isInjective(map1))
      val newCpts = Remapper.applyRemapping(map1, cpts)
      if(showTransitions) println("newCpts = "+StateArray.show(newCpts)) 
      result2 += ((newCpts, unifs, ix))
    }
  }

  // ========= Secondary induced transitions

  /** Get information about secondary induced transitions: pairs (map2,i) such
    * that map2 extends map1 to map cv.principal's identity to match a
    * reference of a secondary component of post, postCpts(i). */ 
  private def getSecondaryInfo(map1: RemappingMap)
      : ArrayBuffer[(RemappingMap, Int)] = {
    val result = new ArrayBuffer[(RemappingMap, Int)]; var ar = acquiredRefs
    while(ar.nonEmpty){
      val (i,(t,id)) = ar.head; ar = ar.tail
      assert(t == cvpf); val id1 = map1(t)(cvpid)
      // Check extending map1 with cvpid -> id is consistent: either (1) it's
      // already there; or (2) map1 is undefined on cvpid, id isn't in the
      // range, and id isn't an identity in pre (which would imply
      // unification).
      if(id1 == id ||
          id1 < 0 && !preCptIds(t)(id)/*.contains((t,id))*/ && !map1(t).contains(id) ){
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
