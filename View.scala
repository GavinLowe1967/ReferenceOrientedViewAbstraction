package ViewAbstraction

import collection.ShardedHashSet
import ox.gavin.profiling.Profiler

/** A minimal ComponentView.  Used where it's useful to use less memory. */
class ReducedComponentView(
  val servers: ServerStates, val components: Array[State]){

  // Profiler.count("ReducedComponentView") // 1.3B with lazySetNoJoined.csp!

  /** The principal component. */
  def principal = components(0)

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
