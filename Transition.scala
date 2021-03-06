package ViewAbstraction

import ox.gavin.profiling.Profiler

/** A transition, representing pre -e-> post. */
class Transition(
  val pre: Concretization, val e: EventInt, val post: Concretization){

  /** The servers in the pre-state. */
  val preServers = pre.servers

  /** Do the servers change state? */
  val changedServers = preServers != post.servers

  private val cptsLength = pre.components.length

  /** Bit map indicating which components have changed state. */
  val changedStateBitMap = { 
    val changedStateBitMap = new Array[Boolean](cptsLength); var i = 0
    while(i < cptsLength){
      changedStateBitMap(i) = pre.components(i) != post.components(i); i += 1
    }
    changedStateBitMap
  }

/*
  /** Bit map indicating which components have changed state, stored as an
    * Int. */
  private val changedStateBits: Int = {
    var csb = 0; var mask = 1; var i = 0
    while(i < cptsLength){
      if(pre.components(i) != post.components(i)) csb += mask
      mask += mask; i += 1
    }
    csb
  }
 */

  /** Has component i changed state? */
  //def changedStateBitMap(i: Int) = (changedStateBits | (1 << i)) != 0

  /** The control states of pre. */
  //private val preCptCS: Array[ControlState] = pre.components.map(_.cs)

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
  private val newServerIds: Array[Array[Boolean]] = 
    ServerStates.newParamsBitMap(preServers, post.servers)

  /** All parameters in post.servers but not in pre.servers, as a bitmap. */
  def getNewServerIds: Array[Array[Boolean]] = {
    // Note: need to clone
    val nsi = new Array[Array[Boolean]](numTypes); var t = 0
    while(t < numTypes){ nsi(t) = newServerIds(t).clone; t += 1 }
    nsi
  }

  /** Do the servers acquire any new parameter? */
  val serverGetsNewId = {
    // Search if any field of newServerIds is set
    var res = false; var t = 0
    while(t < numTypes && !res){
      var i = 0; val len = newServerIds(t).length
      while(i < len && !newServerIds(t)(i)) i += 1
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
    * and not matching any parameter of pre. */
  val acquiredRefs: Array[List[(Int,Parameter)]] = {
    val aRefs = Array.fill(numTypes)(List[(Int,Parameter)]()); var t = 0
    while(t < numTypes){
      var i = 1
      while(i < cptsLength){
        if(changedStateBitMap(i)){
          val preCpt = pre.components(i); val postCpt = post.components(i)
          //if(preCpt != postCpt){
          var j = 1
          while(j < postCpt.length){
            val p1@(t1,x) = postCpt.processIdentity(j)
            if(t1 == t && !isDistinguished(x) && !preCpt.hasParam(t,x))
              aRefs(t) ::= (i,p1)
            j += 1
          }
        }
        i += 1
      } // end of inner while
      t += 1
    }
    aRefs
  }

  /** For each type t, could a secondary component gain a reference to a
    * component of type t? */
  val anyAcquiredRefs: Array[Boolean] = acquiredRefs.map(_.nonEmpty)

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
  
  import Unification.UnificationList // = List[(Int,Int)]

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


object Transition{
// [137(N1) || 140(T1) || 146(N2) || 147(Null) || 151() || 152()] ||
//   [128(T2,N3,N2) || 26(N2,T2,N3,N1) || 6(N4)] 
//   -initNode.T2.N4.A.N3.N2->
//   [137(N1) || 140(T1) || 146(N2) || 147(Null) || 151() || 155(N4,N3)] || 
//     [129(T2,N4,N3,N2) || 26(N2,T2,N3,N1) || 9(N4,N3,N2)])

  /** Function used when debugging.  The transition that should induce the 
    * missing view. 
    * [137(N1) || 140(T1) || 146(N1) || 147(Null) || 151() || 152()] ||
    *   [59(T2,N2,N3,N4) || 14(N4,T2,N2,N3)] -->
    * [137(N1) || 140(T1) || 146(N1) || 147(Null) || 151() || 154(N4,N2,N3)] ||
    *   [60(T2,N2,N3,N4) || 14(N4,T2,N3,N3)]*/
  def highlight(trans: Transition) = 
    ComponentView0.highlightServers0(trans.preServers) &&
      trans.preServers.servers(5).cs == 152 && {
        val princ = trans.pre.components(0)
        princ.cs == 59 && princ.ids.sameElements(Array(1,1,2,3))
      } && {
        val second = trans.pre.components(1)
        second.cs == 14 && second.ids.sameElements(Array(3,1,1,2))
      } && {
        val postServers = trans.post.servers
        ComponentView0.highlightServers0(postServers) &&
        postServers.servers(5).cs == 154 && 
        postServers.servers(5).ids.sameElements(Array(3,1,2))
      }

}
