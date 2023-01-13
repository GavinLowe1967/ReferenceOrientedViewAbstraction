package ViewAbstraction

import ox.gavin.profiling.Profiler

/** A transition, representing pre -e-> post. */
class Transition(
  val pre: Concretization, val e: EventInt, val post: Concretization)
extends TransitionT{
  Profiler.count("Transition")

  /** Do the servers change state? */
  def changedServers = preServers != post.servers

  private def cptsLength = pre.components.length

  /** Bit map indicating which components have changed state. */
  private val changedStateBitMapB: ByteBitMap.ByteBitMap = {
    var csbb = ByteBitMap.Empty; var i = 0
    while(i < cptsLength){
      if(pre.components(i) != post.components(i)) csbb = ByteBitMap.set(csbb, i)
      i += 1
    }
    csbb
  }

  def changedStateBitMap(i: Int) = ByteBitMap.get(changedStateBitMapB, i)


  /** The control states in pre of components that change state. */
  val changingCptCS: Array[ControlState] = {
    var res = List[ControlState](); var i = cptsLength
    while(i > 0){
      i -= 1
      if(changedStateBitMap(i)){
        val cs = pre.components(i).cs
        if(!res.contains(cs)) res ::= cs
      }
    }
    res.toArray
    // IMPROVE: use ArrayBuffer or Array
  }

  private val changingCSLen = changingCptCS.length


  // ==================================================================
  // Things relating to parameters

  /** All parameters in post.servers but not in pre.servers, as a bitmap. */
  private val newServerIds: IdentitiesBitMap.IdentitiesBitMap = 
    ServerStates.newParamsIdentitiesBitMap(preServers, post.servers)
  // private val newServerIds: Array[Array[Boolean]] = 
  //   ServerStates.newParamsBitMap(preServers, post.servers)

  /** All parameters in post.servers but not in pre.servers, as a bitmap. */
  def getNewServerIds: Array[Array[Boolean]] =
    IdentitiesBitMap.toArrayBitMap(newServerIds)
  //  {
  //   // Note: need to clone
  //   val nsi = new Array[Array[Boolean]](numTypes); var t = 0
  //   while(t < numTypes){ nsi(t) = newServerIds(t).clone; t += 1 }
  //   nsi
  // }

  /** Do the servers acquire any new parameter? */
  val serverGetsNewId = {
    // Search if any field of newServerIds is set
    var res = false; var t = 0
    while(t < numTypes && !res){
      var i = 0; val len = typeSizes(t) // newServerIds(t).length
      while(i < len && !IdentitiesBitMap(newServerIds,t,i)) i += 1
      res = i < len; t += 1
    }
    res
  }

  /** A NextArgMap, containing values greater than anything in pre or post. */
  private val nextArg: NextArgMap = pre.getNextArgMap
  post.updateNextArgMap(nextArg)

  /** A NextArgMap, containing values greater than anything in pre or post. */
  def getNextArgMap = nextArg.clone

  /** For each type t, a representation of all parameters of secondary
    * components that could gain a reference to a component of type t: all
    * pairs (i,p1) such that pre.components(i) changes state in the transition
    * (with (i>0), and p1 is a new parameter of post.components(i), of type t,
    * for which views are considered, and not matching any parameter of
    * pre. */
  //val acquiredRefs: Array[Array[(Int,Parameter)]] = {
  private val acquiredRefsCompressed: Array[Array[Short]] = {
    val aRefs = Array.fill(numTypes)(List[Short]()); var t = 0
    while(t < numTypes){
      var i = 1
      while(i < cptsLength){
        if(changedStateBitMap(i)){
          val preCpt = pre.components(i); val postCpt = post.components(i)
          var j = 1
          while(j < postCpt.length){
            if(postCpt.includeParam(j)){
              val p1@(t1,x) = postCpt.processIdentity(j)
              if(t1 == t && !isDistinguished(x) && !preCpt.hasParam(t,x))
                aRefs(t) ::= Transition.acquiredRefToShort(i,p1)
            }
            j += 1
          }
        }
        i += 1
      } // end of inner while
      t += 1
    }
    aRefs.map(_.toArray)
  }


  def acquiredRefs: Array[Array[(Int,Parameter)]] = 
    acquiredRefsCompressed.map(_.map(Transition.shortToAcquiredRef))

  /** A Byte recording information about, for each type t, could a secondary
    * component gain a reference to a component of type t? */
  private val anyAcquiredRefsB: ByteBitMap.ByteBitMap = {
    var aar = ByteBitMap.Empty
    for(t <- 0 until numTypes; if acquiredRefs(t).nonEmpty) 
      aar = ByteBitMap.set(aar, t)
    aar
  }

  /** An Int recording information about, for each type t, could a secondary
    * component gain a reference to a component of type t? As used in
    * ServerBasedViewSet.iterator. */
  def anyAcquiredRefsInt: Int = anyAcquiredRefsB.toInt

  // val anyAcquiredRefsA: Array[Boolean] = acquiredRefs.map(_.nonEmpty)

  // assert(ServerBasedViewSet.boolArrayToInt(anyAcquiredRefsA) == anyAcquiredRefsInt,
  //   s"anyAcquiredRefsA = "+anyAcquiredRefsA.mkString(",")+
  //     "\n"+ServerBasedViewSet.boolArrayToInt(anyAcquiredRefsA)+", "+anyAcquiredRefsInt)

  /** Could a secondary component gain a reference to a component of type t? */
  def anyAcquiredRefs(t: Type) = acquiredRefs(t).nonEmpty 
  // ByteBitMap.get(anyAcquiredRefsB, t)

  /** Which components change state and acquire a reference? */
  private val referenceAcquirers: Array[Boolean] = {
    val ra = new Array[Boolean](cptsLength)
    for(t <- 0 until numTypes; (i,_) <- acquiredRefs(t)) ra(i) = true
    ra
  }

  // ==================================================================
  // Things relating to unification


  /** Might there be sufficient unifications with a view with components cpts to
    * give at least one induced transition?  Either (1) we're using singleRef
    * and a secondary component might acquire a reference to cpts(0); (2) the
    * servers acquire a new reference; (3) the servers change state, and we
    * haven't previously recorded a similar transition; or (4) a state of cpts
    * has the same control state as a component that changes state in this
    * transition. */
  def mightGiveSufficientUnifs(cv: ComponentView): Boolean = {
    // val cpts = cv.components
    val cvInfo = cv.mightGiveSufficientUnifsInfo
    singleRef && anyAcquiredRefs(cvInfo.princFamily) ||         // case (1)
    serverGetsNewId ||                                          // case (2)
    changedServers && !cv.containsDoneInduced(post.servers) ||  // case (3)
    possibleUnification(cvInfo)                                 // case (4)
  }
  // Profiling from lazySet bound 44: case 1 true: 20,870,708 + 1,132,780 =
  // 22,003,488; case 2 first true 3,032,522; case 3 first true 4,030,617;
  // case 4 first true 11,478,237; all false 3,296,727,447

  /** Might a component of cpts be unified with a component of pre.components
    * that changes state?  More precisely, do they have the same control
    * state? */
  @inline private 
  def possibleUnification(cvInfo: ComponentView0.MightGiveSufficientUnifsInfo)
      : Boolean = {
    var i = 0
    while(i < changingCSLen && !cvInfo.hasControlState(changingCptCS(i)))
      i += 1
    i < changingCSLen
    // while(i < cptsLength && 
    //     (!changedStateBitMap(i) || !cvInfo.hasControlState(preCptCS(i))))
    //   i += 1
    // i < cptsLength
  }
  
  // import Unification.UnificationList // = List[(Int,Int)]

  type UnificationList = List[(Int,Int)] 

  /** Given unification list unifs, is the principal unified with a component
    * that changes state and acquires a reference? */
  def doesPrincipalAcquireRef(unifs: UnificationList): Boolean = 
    unifs.exists{ case (j,i) => j == 0 && referenceAcquirers(i) }

  /** Given unifications unifs and a view of length len, get the post-states of
    * unified components that change state, or null if none. */
  def getPostUnified(unifs: UnificationList, len: Int): List[State] = {
    val postUnified = new Array[State](len); var found = false
    for(j <- 0 until len){
      // Indices of cpts of pre unified with cpts(j)
      val is = unifs.filter(_._1 == j)
      if(is.nonEmpty){
        assert(is.length == 1); val i = is.head._2
        if(changedStateBitMap(i)){
          postUnified(j) = post.components(i); found = true
        }
      }
    }
    if(found) postUnified.toList else null
  }

  /** Does unifs represent a unification in which a unified component changes
    * state? */
  def isChangingUnif(unifs: UnificationList): Boolean = {
    var us = unifs
    while(us.nonEmpty && !changedStateBitMap(unifs.head._2)) us = us.tail
    us.nonEmpty
  }

  /** Memory profile. */
  def memoryProfile = {
    import ox.gavin.profiling.MemoryProfiler.traverse
    traverse("Transition pre", pre, maxPrint = 1)
    traverse("Transition post", post, maxPrint = 1)
    traverse("Transition", this, maxPrint = 1)
  }

  // ==================================================================
  // Overriding standard things.

  override def toString = s"$pre\n  -${showEvent(e)}->\n  $post"

  /** Equality. */
  override def equals(that: Any) = that match{
    case tr: Transition => pre == tr.pre && e == tr.e && post == tr.post
  }

  override def hashCode = 
    (pre.hashCode ^ e) + 73*post.hashCode 
}


// ==================================================================

object Transition{
  /** The number of bits used for pid in acquiredRefToShort. */
  private val ProcessIdBits = LogMaxNumTypes+ProcessIdentityShift // 11

  /** Bit mask used in acquiredRefToShort. */
  private val PIDBitMask = (1 << ProcessIdBits) - 1

  /** Maximum value for i in acquiredRefToShort. */
  private val MaxIndex = (1 << (15-ProcessIdBits)) - 1 // 15

  /** Encode the pair (i, pid) as a Short. */
  @inline private def acquiredRefToShort(i: Int, pid: ProcessIdentity): Short = {
    assert(i <= MaxIndex, s"i = $i, MaxIndex = $MaxIndex") // Should have i <= 3
    ((i << ProcessIdBits) + processIdentityToShort(pid)).toShort
  }

  @inline private def shortToAcquiredRef(s: Short) = {
    val pidBits = (s & PIDBitMask).toShort
    (s >> ProcessIdBits, shortToProcessIdentity(pidBits))
  }

  // def check(i: Int, pid: ProcessIdentity) = 
  //   assert(shortToAcquiredRef(acquiredRefToShort(i,pid)) == (i,pid), (i,pid))
  // check(0,(0,0));
  // check(MaxIndex, ((1 << LogMaxNumTypes)-1, (1 << ProcessIdentityShift)-1))


  /* Functions used when debugging, to highlight the transition that should
   * induce the missing view. */

  /** The pre-state servers of the relevant transition. 
    * [107(N0) || 109(N1) || 110() || 114(T0) || 119() || 1()]. */
  def highlightPreServers(preServers: ServerStates) = 
    ComponentView0.highlightServers0(preServers) && preServers(4).cs == 119

  /** The pre-state components of the relevant transition
    * [75(T0,N0,N1,N2) || 14(N0,N1,Null)] */
  def highlightPreCpts(cpts: Array[State]) = {
    val princ = cpts(0)
    princ.cs == 75 && princ.ids.sameElements(Array(0,0,1,2)) && {
      val second = cpts(1)
      second.cs == 14 && second.ids.sameElements(Array(0,1,-1))
    }
  }

  /** Function used when debugging.  The transition that should induce the 
    * missing view. 
    * [107(N0) || 109(N1) || 110() || 114(T0) || 119() || 1()] ||
    *    [75(T0,N0,N1,N2) || 14(N0,N1,Null)] -->
    * [107(N0) || 109(N1) || 110() || 114(T0) || 121(T0,N0,N1) || 1()] ||
    *    [77(T0,N0,N1,N2) || 14(N0,N2,Null)]*/
  def highlight(trans: Transition) = {
    val pre = trans.pre
    highlightPreServers(trans.preServers) && highlightPreCpts(pre.components)
  }
}
