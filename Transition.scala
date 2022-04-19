package ViewAbstraction

import ox.gavin.profiling.Profiler

/** A transition, representing pre -e-> post. */
class Transition(
  val pre: Concretization, val e: EventInt, val post: Concretization){

  /** Do the servers change state? */
  val changedServers = pre.servers != post.servers

  private val cptsLength = pre.components.length

/*
  /** Bit map indicating which components have changed state. */
  val changedStateBitMap = { 
    val changedStateBitMap = new Array[Boolean](cptsLength); var i = 0
    while(i < cptsLength){
      changedStateBitMap(i) = pre.components(i) != post.components(i); i += 1
    }
    changedStateBitMap
  }
 */

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

  /** Has component i changed state? */
  def changedStateBitMap(i: Int) = (changedStateBits | (1 << i)) != 0

  /** The control states of pre. */
  private val preCptCS: Array[ControlState] = pre.components.map(_.cs)

  // ==================================================================
  // Things relating to parameters

  /** All parameters in post.servers but not in pre.servers, as a bitmap. */
  private val newServerIds: Array[Array[Boolean]] = 
    ServerStates.newParamsBitMap(pre.servers, post.servers)

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
  private val anyAcquiredRefs: Array[Boolean] = acquiredRefs.map(_.nonEmpty)

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
    serverGetsNewId ||                                      // case (2)
    changedServers &&                                       // case (3)
      (singleRef && !newEffectOn || !cv.containsDoneInduced(post.servers)) ||
    possibleUnification(cvInfo)                               // case (4)
  }
  // Profiling from lazySet bound 44: case 1 true: 20,870,708 + 1,132,780 =
  // 22,003,488; case 2 first true 3,032,522; case 3 first true 4,030,617;
  // case 4 first true 11,478,237; all false 3,296,727,447

  /** Might a component of cpts be unified with a component of pre.components?
    * More precisely, do they have the same control state? */
  @inline private 
  def possibleUnification(cvInfo: ComponentView.MightGiveSufficientUnifsInfo) = {
    var i = 0
    while(i < cptsLength && 
        (!changedStateBitMap(i) || !cvInfo.hasControlState(preCptCS(i))))
      i += 1
    i < cptsLength
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

  override def toString = s"$pre -${SystemP.System.showEvent(e)}->\n  $post"

  /** Equality. */
  override def equals(that: Any) = that match{
    case tr: Transition => pre == tr.pre && e == tr.e && post == tr.post
  }

  override def hashCode = 
    (pre.hashCode ^ e) + 73*post.hashCode 
}
