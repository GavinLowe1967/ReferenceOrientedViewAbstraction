package ViewAbstraction

import ox.gavin.profiling.Profiler

/** Superclass of views of a system state. */
//abstract class View{
  // /** This view was created by the extended transition pre -e-> post. */
  // private var pre, post: Concretization = null
  // private var e: EventInt = -1

  // /** Ingredients for making an extended transition.  If this contains a tuple
  //   * (pre1, cpts, cv, post1, newCpts) then this was created by the extended
  //   * transition 
  //   * mkExtendedPre(pre1, cpts, cv) -e1-> mkExtendedPost(post1, newCpts). 
  //   * We lazily avoid creating these concretizations until needed. */ 
  // private var creationIngredients: 
  //     (Concretization, Array[State], ComponentView, Concretization, Array[State])
  // = null

  // /** Get the creation information for this. */
  // def getCreationInfo: (Concretization, EventInt, Concretization) = 
  //   if(pre != null) (pre, e, post) 
  //   else{ 
  //     val (pre1, cpts, cv, post1, newCpts) = creationIngredients
  //     (mkExtendedPre(pre1, cpts, cv), e, mkExtendedPost(post1, newCpts))
  //   }

  // def getCreationIngredients = creationIngredients

  // /** Record that this view was created by the extended transition 
  //   * pre1 -e1-> post1. */
  // def setCreationInfo(pre1: Concretization, e1: EventInt, post1: Concretization)
  // = {
  //   require(creationIngredients == null && pre == null)
  //   pre = pre1; e = e1; post = post1
  // }

  // /** Record that this view was created by the extended transition
  //   * mkExtendedPre(pre1, cpts, cv) -e1-> mkExtendedPost(post1, newCpts).
  //   */
  // def setCreationInfoIndirect(
  //   pre1: Concretization, cpts: Array[State], cv: ComponentView,
  //   e1: EventInt, post1: Concretization, newCpts: Array[State]) 
  // = {
  //   creationIngredients = (pre1, cpts, cv, post1, newCpts); e = e1
  // }

  // /** Make the extended pre-state by extending pre1 with cpts, and setting cv as
  //   * the secondary view. */
  // private def mkExtendedPre(
  //   pre1: Concretization, cpts: Array[State], cv: ComponentView)
  //     : Concretization = {
  //   val extendedPre = new Concretization(pre1.servers,
  //     StateArray.union(pre1.components, cpts))
  //   extendedPre.setSecondaryView(cv, null)
  //   extendedPre
  // }

  // /** Make the extended post-state by extending post1 with newCpts. */
  // private def mkExtendedPost(post1: Concretization, newCpts: Array[State]) = 
  //   new Concretization(post1.servers, 
  //     StateArray.union(post1.components, newCpts))

  // def showCreationInfo: String = creationIngredients match{
  //   case (pre1, cpts, cv, post1, newCpts) => s"induced by $pre1 -> $post1 on $cv"
  //   case null => s"produced by $pre -> $post"
  // }

  // /** Was this induced by a transition from cv1?  Used in trying to understand
  //   * why so many induced transitions are redundant. */
  // def inducedFrom(cv1: ComponentView) = 
  //   creationIngredients != null && creationIngredients._3 == cv1
//}

// =======================================================

/** A minimal ComponentView.  Used where it's useful to use less memory. */
class ReducedComponentView(
  val servers: ServerStates, val components: Array[State])
    /*extends View*/{

  /** The principal component. */
  def principal = components(0)

  /** The complete ComponentView corresponding to this. */
  //def asComponentView = new ComponentView(servers, components)

  override def equals(that: Any) = {
    if(that != null){
      val cv = that.asInstanceOf[ReducedComponentView]
      servers == cv.servers && sameCpts(cv.components)
    }
    else false
  }

  @inline private def sameCpts(cpts: Array[State]) = {
    val len = components.length
    if(cpts.length == len){
      var i = 0
      while(i < len && components(i) == cpts(i)) i += 1
      i == len
    }
    else false
  }

  /** Create hash code. */
  @inline private def mkHashCode = {
    StateArray.mkHash(servers.hashCode, components)
    // var h = servers.hashCode
    // var i = 0; var n = components.length
    // while(i < n){ h = h*71+components(i).hashCode; i += 1 }    
    // h 
  }

  override val hashCode = mkHashCode

 /** Ordering on ReducedComponentViews.  Return a value x s.t.: x < 0 if this <
    * that; x == 0 when this == that; x > 0 when this > that. */
  def compare(that: ReducedComponentView) = {
    val serverComp = servers.compare(that.servers)
    if(serverComp != 0) serverComp
    else StateArray.compare(components, that.components)
  }

}

// =======================================================

/** Companion object. */
object View{
  def show(servers: ServerStates, states: Array[State]) =
    servers.toString+" || "+StateArray.show(states)

  /** A bound on the values of each type in servers and cpts. */
  @inline def getParamsBound(servers: ServerStates, cpts: Array[State])
      : Array[Int] = {
    val pb = servers.paramsBound.clone
    for(cpt <- cpts){
      val pb1 = cpt.getParamsBound
      for(t <- 0 until numTypes) pb(t) = pb(t) max pb1(t)
    }
    pb
  }
}
