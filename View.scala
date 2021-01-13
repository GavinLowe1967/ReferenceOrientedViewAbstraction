package ViewAbstraction

/** Superclass of views of a system state. */
abstract class View{
  /** This view was created by the extended transition pre -e-> post. */
  var pre, post: Concretization = null
  var e: EventInt = -1

  /** Record that this view was created by the extended transition 
    * pre1 -e1-> post1. */
  def setCreationInfo(pre1: Concretization, e1: EventInt, post1: Concretization) 
  = {
    pre = pre1; e = e1; post = post1
  }
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
    assert(princRefs.forall(
      pid => (
        otherPids.contains(pid) || pid == principal.componentProcessIdentity)
      ) &&
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

  /** The union of cpts1 and cpts2.  Pre: they agree on components with common
    * identities. */
  def union(cpts1: Array[State], cpts2: Array[State]): Array[State] = {
    val ids1 = cpts1.map(_.componentProcessIdentity)
    require(cpts2.forall(st => 
      !ids1.contains(st.componentProcessIdentity) || cpts1.contains(st)))
    cpts1 ++ cpts2.filter(st => !ids1.contains(st.componentProcessIdentity))
  }

  /** Check components in cpts are distinct. */
  def checkDistinct(cpts: Array[State], msg: => String = "") = 
    for(i <- 0 until cpts.length; j <- i+1 until cpts.length)
      assert(cpts(i) != cpts(j), showStates(cpts)+" "+msg)

}

// =======================================================

/** A concretization. */
class Concretization(val servers: ServerStates, val components: Array[State]){ 

  /** Make a ComponentView from this, with components(0) as the principal
    * component.  Note: not in canonical form IMPROVE. */
  def toComponentView: ComponentView = getViewOf(components(0))

  /** Get the view of this with princ as principal component.  Pre: this
    * includes all the components referenced by princ. Note: not in canonical
    * form IMPROVE. */
// FIXME: I think this goes wrong if princ has two references to the same
// component.
  def getViewOf(princ: State): ComponentView = {
    val princIds = princ.ids
    // Other components to be included in the ComponentView: those referenced 
    // by princ
    val components1 = components.tail.filter{cpt =>
      val (f,id) = cpt.componentProcessIdentity
      (1 until princIds.length).exists{j => 
        princIds(j) == id && princ.typeMap(j) == f}
    }
    // Check all princ's references included
    val cIds = components1.map(_.id)
    assert(princ.ids.tail.forall(id => isDistinguished(id) || cIds.contains(id)),
      s"\nConcretization.getViewOf: Not all references of $princ included in\n"+
        this)
    new ComponentView(servers, princ, components1)
  }

  /** In the case that this was created by extending one view with a component
    * from a secondary view, that secondary view. */
  private var secondaryView: ComponentView = null

  def setSecondaryView(sv: ComponentView) = {
    assert(secondaryView == null); secondaryView = sv
  }

  def getSecondaryView = secondaryView

  override def toString = 
    s"$servers || ${components.mkString("[", " || ", "]")}"

  /** A new concretization, extending this with component newState. */
  def extend(newState: State): Concretization =
    new Concretization(servers, components :+ newState)

  override def equals(that: Any) = that match{
    case c: Concretization => 
      servers == c.servers && components.sameElements(c.components)
  }

  def matches(that: View) = that match{
    case cv: ComponentView =>
      servers == cv.servers && components.sameElements(cv.components)
  }
}

// =======================================================

object Concretization{
  /** Make a concretization from cv. */
  def apply(cv: ComponentView) =
    new Concretization(cv.servers, cv.principal +: cv.others)

  def apply(servers: ServerStates, principal: State, others: Array[State]) =
    new Concretization(servers, principal +: others)


}
