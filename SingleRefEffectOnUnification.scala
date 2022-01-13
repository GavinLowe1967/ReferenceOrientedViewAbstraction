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
   * |--makePrimaryExtension
   * |  |--RemappingExtender.makeExtensions
   * |--makeSecondaryExtension
   * |  |--RemappingExtender.makeExtensions
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

  /** The object responsible for extending result-defining mappings. */
  val remappingExtender = new RemappingExtender(pre, post, cv)

  /** Bit map indicating which components have changed state. */
  private val changedStateBitMap = { 
    val changedStateBitMap = new Array[Boolean](preCpts.length); var i = 0
    while(i < preCpts.length){
      changedStateBitMap(i) = preCpts(i) != postCpts(i); i += 1
    }
    changedStateBitMap
  }

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
        // Primary result-defining maps
        val rdMaps = extendToRDMap(map1,otherArgsBitMap)
        // Extend with extra linkages and fresh parameters
        for(rdMap <- rdMaps) makePrimaryExtension(unifs, otherArgsBitMap, rdMap)
      }
      // else println("Not sufficient unif "+unifs)

      //Secondary induced transitions
// IMPROVE: inside "if"?  
      val secondaryInfo = getSecondaryInfo(map1)
      for((map2, i) <- secondaryInfo){
        println("secondary")
        val sc = postCpts(i)
        val otherArgsBitMap = mkSecondaryOtherArgsMap(map2, sc)
        val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
        // Secondary result-defining maps
        val rdMaps = new ArrayBuffer[RemappingMap]
        remappingExtender.extendMapOverComponent(map2, cpts(0), otherArgs, rdMaps)
        // Then consider linkages
        for(rdMap <- rdMaps) 
          makeSecondaryExtension(unifs, otherArgsBitMap, rdMap, i)
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

  /* Extend the result-defining map rdMap, based on unifications unifs, to
   * produce all primary representative extensions.  For each such map, add an
   * appropriate tuple to result. */
  private def makePrimaryExtension(
    unifs: UnificationList, resultRelevantParams: BitMap, rdMap: RemappingMap)
  = {
    val extensions = new ArrayBuffer[RemappingMap]
    remappingExtender.makeExtensions(unifs, resultRelevantParams, rdMap, List(), extensions)
    for(map1 <- extensions){
      if(debugging) assert(Remapper.isInjective(map1))
      val newCpts = Remapper.applyRemapping(map1, cpts)
      val reducedMapInfo: ReducedMap =
        if(unifs.isEmpty) Remapper.rangeRestrictTo(map1, postServers)
        else null
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
    val extensions = new ArrayBuffer[RemappingMap]
    remappingExtender.makeExtensions(unifs, resultRelevantParams, rdMap, List(), extensions)
    for(map1 <- extensions){
      if(debugging) assert(Remapper.isInjective(map1))
      val newCpts = Remapper.applyRemapping(map1, cpts)
      result2 += ((newCpts, unifs, ix))
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

    /** Extend the result-defining map rdMap, based on unifications unifs, to
      * produce all representative extensions, recursively mapping parameters
      * based on linkages, and then mapping other parameters to fresh
      * parameters. Return all resulting maps. */
    def extendPrimaryMapping(
      unifs: UnificationList, otherArgs: BitMap, rdMap: RemappingMap)
        : ArrayBuffer[RemappingMap] = {
      result.clear
      // outer.extendMapping(unifs, otherArgs, rdMap, None)
      outer.makePrimaryExtension(unifs, otherArgs, rdMap)
      val res = result.map(_._1); result.clear; res
    }

    def extendSecondaryMapping(
      unifs: UnificationList, otherArgs: BitMap, 
      rdMap: RemappingMap, i: Int)
        : ArrayBuffer[Array[State]] = {
      result2.clear
      outer.makeSecondaryExtension(unifs, otherArgs, rdMap, i)
      // outer.extendMapping(unifs, otherArgs, rdMap, Some(i))
      val res = result2.map(_._1); result2.clear; res
    }

    val acquiredRefs = outer.acquiredRefs 

    val getSecondaryInfo = outer.getSecondaryInfo _

    val extendMapOverComponent = outer.remappingExtender.extendMapOverComponent _

    def makeExtensions(unifs: UnificationList, resultRelevantParams: BitMap, 
      rdMap: RemappingMap)
        : ArrayBuffer[RemappingMap] = {
      val result = new ArrayBuffer[RemappingMap]
      outer.remappingExtender.makeExtensions(unifs, resultRelevantParams, rdMap, List(), result)
      result
    }

  } // end of TestHooks
}
