package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet}

/** Object responsible for the unification of cv with trans.pre, suitable for
  * calculating transitions induced by trans upon cv. */
class EffectOnUnification(trans: Transition,  cv: ComponentView){
  require(!singleRef) // require(!newEffectOn)

  import Unification.CombineResult
    // = ArrayBuffer[(RemappingMap, Array[State], UnificationList)]
  import EffectOnUnification.MatchingTuple

  /* Relationship of main functions:
   * 
   * apply
   * |--Unification.allUnifs
   * |--isSufficientUnif
   * |--mkOtherArgsBitMap
   * |  |--addIdsFromNewRef
   * |--extendUnif
   * |  |--Unification.combine1
   * 
   * Following is dead
   * |--extendUnifSingleRef                    (~95% of time with lazySet)
   *    |--EffectOnUnification.remapToCreateCrossRefs  (~25%)
   *    |--getOtherArgsBitMapForSingleRef              (~12%)
   *    |--Unification.getCombiningMaps                (~25%)
   *    |--makeSecondaryInducedTransitions             (~10%)
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
  if(debugging) StateArray.checkDistinct(cpts)
  private val (cvpf, cvpid) = cv.principal.componentProcessIdentity

  // IMPROVE
  private val highlight = false &&
    preCpts.length == 2 && preCpts(0).cs == 15 && preCpts(1).cs == 7 &&
      cpts(0).cs == 8 && cpts(0).ids(0) == 1
    // pre.servers.servers(1).cs == 100 && post.servers.servers(5).cs == 113 &&
    //   preCpts.length == 2 && cv.components.length == 2 &&
    //   preCpts(0).cs == 66 && preCpts(1).cs == 13 && preCpts(1).ids(2) == 3 &&
    //   preCpts.sameElements(cv.components)

  /** Identities of components of pre. */
  private val preIds = 
    Array.tabulate(preCpts.length)(i => preCpts(i).componentProcessIdentity)

  /** Identities of components of cv. */
  private val cvIds =
    Array.tabulate(cpts.length)(i => cpts(i).componentProcessIdentity)

  /** Identities of components of pre that match the family of cv.principal. */
  private val preMatchingIds = {
    var ids = List[Identity](); var i = 0
    while(i < preCpts.length){
      val c = preCpts(i); i += 1; if(c.family == cvpf) ids ::= c.ids(0)
    }
    ids
  }

  /** For each parameter x of states, the list of positions (component number,
    * parameter number) where x appears.  size gives the number of parameters
    * of each type. */
  private def mkPositionMap(size: Array[Int], states: Array[State])
      : Array[Array[List[(Int,Int)]]] = {
    val pMap = Array.tabulate(numTypes)( t => 
      Array.fill(size(t))(List[(Int,Int)]()) )
    for(i <- 0 until states.length){
      val pids = states(i).processIdentities
      for(j <- 0 until pids.length){
        val (t,x) = pids(j)
        if(!isDistinguished(x)){
          assert(0 <= t && t < pMap.size, s"t = $t")
          assert(0 <= x && x < pMap(t).size, 
            s"x = $x; pMap(t).size = ${pMap(t).size}; pre = $pre")
          pMap(t)(x) ::= (i,j)
        }
      }
    }
    pMap
  }

  /** For each parameter x of preCpts, the list of positions (component number,
    * parameter number) where x appears.  IMPROVE: maybe this should be stored
    * in pre.  */
  private val prePositionMap: Array[Array[List[(Int,Int)]]] = 
    mkPositionMap(pre.getParamsBound, preCpts)
  // IMPROVE
  //for(t <- 0 until numTypes; pairs <- prePositionMap(t))
  // assert(pairs.forall(_._1 < preCpts.length))

  /** For each parameter x of cv, the list of positions (component number,
    * parameter number) where x appears.  IMPROVE: maybe this should be stored
    * in cv.  */
  private val cvPositionMap: Array[Array[List[(Int,Int)]]] = 
    mkPositionMap(cv.getParamsBound, cpts)

  import Unification.UnificationList // = List[(Int,Int)]
  // Contains (i,j) if cpts(i) is unified with preCpts(j)

  // A representation of map |> post.servers
  // import ServersReducedMap.ReducedMap 

  //private type Linkages =  List[RemappingExtender.Linkage]

  import EffectOnUnification.InducedInfo 
   // ArrayBuffer[(RemappingMap, UnificationList, ReducedMap)]

  /** Variable in which we build up the result. */
  private val result = new InducedInfo

  /** A NextArgMap, containing values greater than anything in pre or post. */
  private val nextArg: NextArgMap = pre.getNextArgMap
  post.updateNextArgMap(nextArg)

  /** Bit map indicating which components have changed state. */
  private val changedStateBitMap = getChangedStateBitMap()

  /** All ways of unifying pre and cv.  
    * 
    * Each parameter of cv is remapped (1) as identity function for parameters
    * in pre.servers; (2) if a unification of components is done, as required
    * by that unification; (3) otherwise either (a) to a parameter in
    * post.servers or the post-state of a unified component or the post state
    * of a component to which cv.principal gains a reference, or (b) the next
    * fresh value.  In each case, the remapping is restricted to be injective.
    * Also, under (a), identities cannot be mapped to identities in
    * post.components, other than with unification.  The choice under 3(a) is
    * precisely those variables that will exist in the post-state of cv (and
    * are distinct post symmetry reduction).  
    * 
    * The first component of the returned result contains tuples (map, cpts,
    * unifs) where map is the remapping function, cpts is the remapped
    * components, and a UnificationList that contains (j,i) whenever
    * cv.components(j) unifies with pre.components(i).
    * 
    * The second component of the result contains information concerning
    * secondary induced transitions under singleRef.  In this case, c2Refs
    * contains pairs (i,id) such that post.components(i) gains a reference in
    * parameter id to a value of the same type as cv.principal.id.  For each
    * such (i,id), each parameter of cv is renamed as under (1) or (2) above;
    * or (3) cv.principal.id is renamed to id; (4) every other parameter of
    * cv.principal can be renamed to a parameter in post.servers or a
    * parameter of post.components(i) or the next fresh value.  Each element
    * of the second component of the result contains: the remapped state, the
    * unification list (as above), and the parameter i.
    * 
    * We suppress values that won't give a new view in effectOn.   
    * 
    * @return remapped state, paired with a UnificationList that contains
    * (j,i) whenever cv.components(j) unifies with pre.components(i).  */
  def apply(): InducedInfo = {
    // IMPROVE: some of the initial calculations depends only on pre and post, so
    // could be stored with the transition.
    val changedServers = servers != post.servers
    // Get all ways of unifying pre and cv. 
    val allUs = Unification.allUnifs(pre, cv) // cpts)
    // assert(allUs.distinct.length == allUs.length)
    var ix = 0
    while(ix < allUs.length){
      val (map1, unifs) = allUs(ix); ix += 1
      //if(highlight) println(s"*unifs = $unifs, map1 = "+Remapper.show(map1)) 
      // Do we need to consider this combination?  Described in optimisations
      // in the paper. 
      val sufficientUnif = isSufficientUnif(changedServers, unifs)
      if(sufficientUnif){
        val otherArgsBitMap = mkOtherArgsBitMap(unifs)
        extendUnif(unifs, map1, otherArgsBitMap)
      }
    } // end of while loop
    result
  }

// IMPROVE: do we need all of unifs?
// IMPROVE, try to identify second case for sufficientUnifs within allUnifs,
// by trying to unify components that change state first.
// IMPROVE: can we share work between the calls to extendUnif? 

  /** Test if the current combination in combine needs to be considered.  Either
    * (1) the servers changed, and either (a) we have some unification, or (b)
    * this is the first time for no unification with this combination of cv,
    * pre.servers and post.servers; or (2) the servers are unchanged but we
    * unify with a component that does change state. 
    *  **** Different for singleRef
    * @param changedServers did the servers change state?
    * @paral unifs the list of unifications made. */
  @inline private def isSufficientUnif(
    changedServers: Boolean, unifs: UnificationList)
      : Boolean = {
    // Is there a unification with a component that changes state?
    @inline def changingUnif = {
      var us = unifs; var sufficientUnif = false
      while(!sufficientUnif && us.nonEmpty){
        sufficientUnif = changedStateBitMap(us.head._2); us = us.tail
      }
      sufficientUnif
    }

    if(trans.serverGetsNewId || changingUnif) true
    else changedServers && cv.addDoneInduced(postServers)
  }

  /** Create a bit map corresponding to an OtherArgMap and containing all
    * values: (1) in newServerIds (parameters in post.servers but not
    * pre.servers), or (2) in post.cpts for a unified parameter if not in
    * (pre.)servers; (3) in post.cpts for a component to which cv.principal
    * gains a reference; But excluding parameters of servers in all cases.  */
  @inline private 
  def mkOtherArgsBitMap(unifs: UnificationList): BitMap = {
    // (1) parameters in newServerIds
    val otherArgsBitMap = ServerStates.newParamsBitMap(servers, post.servers)
    var us = unifs
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
        // Assumptions imply pid must be in postCpts, except under singleRef.
        if(c != null) c.addIdsToBitMap(otherArgsBitMap, serverIds)
        else assert(singleRef)
      }
    }
  }

  /** Extend map1 with unifications unifs, corresponding to transitions induced
    * by the transition pre -> post on cv.
    * 
    * Parameters must be remapped consistent with map1.  Parameters undefined
    * in map1 can be mapped: (1) to a parameter in otherArgsBitMap (other than
    * in the range of map1); or (2) a fresh value, given by nextArg.  However,
    * identities cannot be mapped to identities of postCpts (=
    * post.components) (since that would imply unification).  Each remapped
    * state and corresponding unifications is added to result. */
  @inline private def extendUnif(unifs: UnificationList,
    map1: RemappingMap, otherArgsBitMap: BitMap)
      : Unit = {
    // if(debugging) assert(Remapper.isInjective(map1), Remapper.show(map1))
    assert(!singleRef)
    // Remove values in ran map1
    Remapper.removeFromBitMap(map1, otherArgsBitMap)
    // Convert to OtherArgMap
    val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
    // Values that identities can be mapped to: values in otherArgs, but not
    // identities of components in post; update otherArgsBitMap to record.
    StateArray.removeIdsFromBitMap(postCpts, otherArgsBitMap)
    // Create primary induced transitions.
    Unification.combine1(
      map1, otherArgs, otherArgsBitMap, nextArg, unifs, cpts, result)
  } // end of extendUnif

  /** Bitmap showing which components changed state between preCpts and
    * postCpts. */
  @inline private 
  def getChangedStateBitMap(): Array[Boolean] = {
    val changedStateBitMap = new Array[Boolean](preCpts.length); var i = 0
    while(i < preCpts.length){
      changedStateBitMap(i) = preCpts(i) != postCpts(i); i += 1
    }
    changedStateBitMap
  }

}

// ==================================================================

object EffectOnUnification{
  import Unification.UnificationList // = List[(Int,Int)]
  // Contains (i,j) if cpts(i) is unified with preCpts(j)

  /** The result of apply on a companion. */
  type InducedInfo = ArrayBuffer[(RemappingMap, UnificationList)]

  def combine(trans: Transition, cv: ComponentView): InducedInfo = 
    new EffectOnUnification(trans, cv)()

  /** A tuple in a remapping from cpts to preCpts.  Each tuple ((i1,j1),(i2,j2))
    * indicates that parameter j2 of cpts(i2) is mapped to match parameter j1
    * of preCpts(i1).  Precisely one of j1 and j2 equals 0. */
  type MatchingTuple = ((Int,Int), (Int, Int))


  // /** Bit map (indexed by component number, param number) showing which
  //   * parameters of preCpts can be mapped onto within remapToCreateCrossRefs:
  //   * all identities; and non-identities those that are not distinguished, and
  //   * do not match any identity in preCpts. */
  // @inline private def getRangeBitMap(preCpts: Array[State]): BitMap = {
  //   val preIds = Array.tabulate(preCpts.length)(
  //     i => preCpts(i).componentProcessIdentity)
  //   val rangeBitMap = new Array[Array[Boolean]](preCpts.length); var i = 0
  //   while(i < preCpts.length){
  //     val cpt = preCpts(i); rangeBitMap(i) = new Array[Boolean](cpt.length)
  //     rangeBitMap(i)(0) = true; var j = 0 // IMPROVE: j = 1?
  //     while(j < cpt.length){
  //       val (t,p) = cpt.processIdentity(j)
  //       if(!isDistinguished(p) && !preIds.contains((t,p))){
  //         rangeBitMap(i)(j) = true; assert(j != 0)
  //       }
  //       j += 1
  //     } // end of inner while
  //     i += 1
  //   } // end of outer while
  //   rangeBitMap
  // }


  // /** Similar bit map for cpts, showing which params can be mapped: all
  //   * identities; and all non-identities that are not distinguished, and do
  //   * not match any identity in cpts. */
  // @inline private def getDomBitMap(cpts: Array[State]): BitMap = {
  //   val ids = Array.tabulate(cpts.length)(i => cpts(i).componentProcessIdentity)
  //   val domBitMap = new Array[Array[Boolean]](cpts.length); var i = 0
  //   while(i < cpts.length){
  //     val cpt = cpts(i); domBitMap(i) = new Array[Boolean](cpt.length)
  //     domBitMap(i)(0) = true; var j = 0
  //     while(j < cpt.length){
  //       val (t,p) = cpt.processIdentity(j)
  //       if(!isDistinguished(p) && !ids.contains((t,p))) domBitMap(i)(j) = true
  //       j += 1
  //     } // end of inner while
  //     i += 1
  //   } // end of outer while
  //   domBitMap
  // }

  /** Hooks for testing. */
  trait Tester{
    // protected val remapToCreateCrossRefs = 
    //   EffectOnUnification.remapToCreateCrossRefs _ 
  }
}

// =======================================================

