package ViewAbstraction

import collection.ShardedHashSet
import ox.gavin.profiling.Profiler

/** A minimal ComponentView.  Used where it's useful to use less memory. 
  * 
  * Pre: components is stored in StateArray. */
class ReducedComponentView(
  val servers: ServerStates, val components: Array[State]){
// IMPROVE
  //assert(components.eq(StateArray(components)))

  // Profiler.count("ReducedComponentView") // 1.3B with lazySetNoJoined.csp!

  /** The principal component. */
  def principal = components(0)

  override def equals(that: Any) = {
    if(that != null){
      val cv = that.asInstanceOf[ReducedComponentView]
      servers == cv.servers && components == cv.components 
      // Note: the value of components is shared between
      // ReducedComponentViews, so we can use reference equality above.
    }
    else false
  }

  // /** Does this have the same components as cpts? */
  // @inline private def sameCpts(cpts: Array[State]) = {
  //   // Note: I believe that cpts is always the same as StateArray(cpts) here.
  //   // The code below takes advantage of this.
  //   if(cpts == components) true
  //   else{
  //     // If the above is true, the following can be replaced with "false".
  //     val len = components.length
  //     if(cpts.length == len){
  //       var i = 0
  //       while(i < len && components(i) == cpts(i)) i += 1
  //       assert(i != len) 
  //       i == len
  //     }
  //     else false
  //   }
  // }

  /** Is this known to be in the ViewSet? */
  private var found = false

  /** Is this known to be in the ViewSet?  Might give false negative. */
  def isFound = found

  /** Record that this is in the ViewSet. */
  def setFound = found = true

  /** Create hash code. */
  @inline private def mkHashCode = {
    StateArray.mkHash1(servers.hashCode, components)
    // var h = servers.hashCode
    // var i = 0; var n = components.length
    // while(i < n){ h = h*71+components(i).hashCode; i += 1 }    
    // h 
  }

  override def hashCode = mkHashCode

  /** Ordering on ReducedComponentViews.  Return a value x s.t.: x < 0 if this <
    * that; x == 0 when this == that; x > 0 when this > that. */
  @inline def compare(that: ReducedComponentView) = {
    val serverComp = servers.compare(that.servers)
    if(serverComp != 0) serverComp
    else StateArray.compare(components, that.components)
  }

  def < (that: ReducedComponentView) = compare(that) < 0

  override def toString = s"$servers || "+components.mkString("[", " || ", "]")

  def toString0 = 
    servers.toString0+" || "+
      components.map(_.toString0).mkString("[", " || ", "]")
}

// =======================================================

object ReducedComponentView{
  /** A store of ReducedComponentViews created previously. */
  private val store = new ShardedHashSet[ReducedComponentView]

  /** Get a ReducedComponentView corresponding to servers and cpts.  Note: we
    * avoid storing multiple equivalent ReducedComponentViews, to reduce
    * memory usage. */  
  def apply(servers: ServerStates, cpts: Array[State]) = 
    store.getOrAdd(new ReducedComponentView(servers, cpts))

  def size = store.size

}

// ==================================================================

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
