package ViewAbstraction

/** A transition, representing pre -e-> post. */
class Transition(
  val pre: Concretization, val e: EventInt, val post: Concretization){

  /** Do the servers change state? */
  val changedServers = pre.servers != post.servers

  /** Bit map indicating which components have changed state. */
  val changedStateBitMap = { 
    val len = pre.components.length
    val changedStateBitMap = new Array[Boolean](len); var i = 0
    while(i < len){
      changedStateBitMap(i) = pre.components(i) != post.components(i); i += 1
    }
    changedStateBitMap
  }

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
      while(i < pre.components.length){
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

  /** Which components change state and acquire a reference? */
  private val referenceAcquirers: Array[Boolean] = {
    val ra = new Array[Boolean](pre.components.length)
    for(t <- 0 until numTypes; (i,_) <- acquiredRefs(t)) ra(i) = true
    ra
  }

  // ==================================================================
  // Things relating to unification

  /** Might there be sufficient unifications with a view with components cpts to
    * give at least one induced transition?  Either (1) the servers change
    * state, or (2) a state of cpts has the same control state as a component
    * that changes state in this transition, or (3) we're using singleRef and
    * a secondary component might acquire a reference to cpts(0). */
  def mightGiveSufficientUnifs(cpts: Array[State]): Boolean = {
    if(changedServers || (singleRef && acquiredRefs(cpts(0).family).nonEmpty))
      true
    else{
      var i = 0; var result = false
      while(i < pre.components.length && !result){
        if(changedStateBitMap(i)){
          // Does cpts have a state with control state pre.components(i).cs?
          val cs = pre.components(i).cs; var j = 0; val len = cpts.length
          while(j < len && cpts(j).cs != cs) j += 1
          result = j < len
        }
        i += 1
      }
      result
    }
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

  override def toString = s"$pre -${showEvent(e)}->\n  $post"

  /** Equality. */
  override def equals(that: Any) = that match{
    case tr: Transition => pre == tr.pre && e == tr.e && post == tr.post
  }

  override def hashCode = 
    (pre.hashCode ^ e) + 73*post.hashCode 
}
