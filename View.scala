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

  // Check all components referenced by principal are included
  { 
    val princRefs = principal.processIdentities.tail.filter{
      case(f,id) => !isDistinguished(id)}
    val otherPids = others.map(_.componentProcessIdentity)
    assert(princRefs.forall(otherPids.contains(_)) &&
      otherPids.forall(princRefs.contains(_)),
    s"Not a correct ComponentView: $this")
  }

  override def toString = 
    s"$servers || $principal"+
    (if(others.nonEmpty) " || "+others.mkString("[", " || ", "]") else "")

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
  //def alpha(conc: Concretization): List[View] = ???

  def showStates(states: Array[State]) = states.mkString("[", " || ", "]")

  /** Do cpts1 and cpts2 agree on all components with the same identity?
    * Pre: cpts1(i) agrees with cpts2 on any component with the same identity. */
  def agreeOnCommonComponents(cpts1: Array[State], cpts2: Array[State], i: Int)
      : Boolean = {
    require(agreesWithCommonComponent(cpts1(i), cpts2)) // IMPROVE
    var j = 0
    while(j < cpts1.length && 
        // Use precondition to be lazy
        (j == i || agreesWithCommonComponent(cpts1(j), cpts2)) )
      j += 1
    j == cpts1.length // ok
  }

  /** If cpt shares a process identity with cpts, are they the same state? */
  @inline
  def agreesWithCommonComponent(cpt: State, cpts: Array[State]): Boolean = {
    val cptId = cpt.componentProcessIdentity; var j = 0; var ok = true
    while(j < cpts.length && ok){
      val cpt2 = cpts(j)
      if(cpt2.componentProcessIdentity == cptId) ok = cpt == cpt2
      j += 1
    }
    ok
  }

}

// =======================================================

/** A concretization. */
class Concretization(val servers: ServerStates, val components: Array[State]){ 

  /** Make a ComponentView from this, with components(0) as the principal
    * component.  Note: not in canonical form IMPROVE. */
  def toComponentView: ComponentView = {
    val princ = components(0); val princIds = princ.ids
    // println(s"toComponentView $this")
    // println(s"princIds = ${princIds.mkString("[",",","]")}")
    // Other components to be included in the ComponentView: those referenced 
    // by princ
    val components1 = components.tail.filter{cpt =>
      val (f,id) = cpt.componentProcessIdentity
      (1 until princIds.length).exists{j => 
        princIds(j) == id && princ.typeMap(j) == f}
    }
    // println(s"components1 = ${components1.mkString("[",",","]")}")
    // Check all princ's references included
    val cIds = components1.map(_.id)
    assert(princ.ids.tail.forall(id => isDistinguished(id) || cIds.contains(id)))
    new ComponentView(servers, princ, components1)
    // IMPROVE: make canonical before constructing
  }

  override def toString = 
    s"$servers || ${components.mkString("[", " || ", "]")}"

  /** A new concretization, extending this with component newState. */
  def extend(newState: State): Concretization =
    new Concretization(servers, components :+ newState)

}

object Concretization{
  /** Make a concretization from cv. */
  def apply(cv: ComponentView) =
    new Concretization(cv.servers, cv.principal +: cv.others)

  def apply(servers: ServerStates, principal: State, others: Array[State]) =
    new Concretization(servers, principal +: others)


}
