package ViewAbstraction

/** Superclass of views of a system state. */
abstract class View{

}

// =======================================================

/** A component-centric view.
  * @param servers the states of the servers
  * @param principal the principal component state
  * @param others the other components, referenced by principal.
  */
class ComponentView(
  val servers: ServerStates, val principal: State, val others: Array[State])
    extends View{
  /** All the components in this view, with the principal component first. */
  val components = principal +: others // IMPROVE

  override def toString = 
    s"$servers || $principal || ${others.mkString("[", " || ", "]")}"

  override def equals(that: Any) = that match{
    case cv: ComponentView => 
      // println(s"equals $this $that") 
      servers == cv.servers && principal == cv.principal && 
      others.sameElements(cv.others)
  }

  override val hashCode = {
    var h = servers.hashCode*71+principal.hashCode
    var i = 0; var n = others.length
    while(i < n){ h = h*71+others(i).hashCode; i += 1 }    
    h 
  }
}


// =======================================================

/** Companion object. */
object View{
  /** All components referenced by principal in states. */
  def referencedStates(principal: State, states: Array[State]): Array[State] = {
    val len = principal.ids.length
    val refed = new Array[State](len-1)
    for(i <- 1 until len){
      val thisId = principal.ids(i)
      val matches = states.filter(_.ids(0) == thisId)
      assert(matches.length == 1)
      refed(i-1) = matches(0)
    }
    refed
  }

  /** All the views of a particular concretization. */
  def alpha(conc: Concretization): List[View] = ???

}

// =======================================================

/** A concretization. */
class Concretization(val servers: ServerStates, val components: Array[State]){ 

  /** Make a ComponentView from this, with components(0) as the principal
    * component.  */
  def toComponentView: ComponentView = {
    val princ = components(0); val princIds = princ.ids
    // Other components to be included in the ComponentView
    val components1 = components.tail.filter{cpt =>
      val (f,id) = cpt.componentProcessIdentity
      servers.serverIds(f).contains(id) || 
      (1 until princIds.length).exists(j => 
        princIds(j) == id && princ.typeMap(j) == f)
    }
    // Check all princ's references included
    val cIds = components1.map(_.id)
    assert(princ.ids.tail.forall(id => isDistinguished(id) || cIds.contains(id)))
    new ComponentView(servers, princ, components1)
    // IMPROVE: make canonical before constructing
  }

  override def toString = 
    s"$servers || ${components.mkString("[", " || ", "]")}"

}

object Concretization{
  /** Make a concretization from cv. */
  def apply(cv: ComponentView) =
    new Concretization(cv.servers, cv.principal +: cv.others)

  def apply(servers: ServerStates, principal: State, others: Array[State]) =
    new Concretization(servers, principal +: others)


}
