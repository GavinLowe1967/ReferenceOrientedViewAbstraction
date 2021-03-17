package ViewAbstraction

import ox.gavin.profiling.Profiler

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

  val componentsList = components.toList

  /** Check all components referenced by principal are included, and no more. */
  // IMRPOVE: this is moderately expensive
  @noinline private def checkValid = { 
    val len = principal.ids.length; val othersLen = others.length; var i = 1
    while(i < len){
      val pid = principal.processIdentity(i)
      if(!isDistinguished(pid._2)){
        // Test if otherPids.contains(pid)
        var j = 0
        while(j < othersLen && others(j).componentProcessIdentity != pid) j += 1
        assert(j < othersLen || pid == principal.componentProcessIdentity,
          s"Not a correct ComponentView: $this")
      }
      i += 1
    }
    // Check all of others referenced by principal
    var j = 0
    while(j < others.length){
      val otherId = others(j).componentProcessIdentity 
      var i = 0
      while(i < len && principal.processIdentity(i) != otherId) i += 1
      assert(i < len, s"Not a correct ComponentView: $this")
      j += 1
    }
  }

  checkValid

  /** Is this representable using the values defined in the script? */
  def representableInScript = 
    servers.representableInScript && principal.representableInScript &&
      others.forall(_.representableInScript)

  override def toString = 
    s"$servers || $principal"+
    (if(others.nonEmpty) " || "+others.mkString("[", " || ", "]") else "")

  def toString0 = 
    s"${servers.toString0} || ${principal.toString0}"+
    (if(others.nonEmpty) 
      " || "+others.map(_.toString0).mkString("[", " || ", "]") 
    else "")

  override def equals(that: Any) = that match{
    case cv: ComponentView => 
      // println(s"equals $this $that") 
      servers == cv.servers && principal == cv.principal && 
      others.sameElements(cv.others)
  }

  /** Create hash code. */
  @inline private def mkHashCode = {
    var h = servers.hashCode*71+principal.hashCode
    var i = 0; var n = others.length
    while(i < n){ h = h*71+others(i).hashCode; i += 1 }    
    h 
  }

  override val hashCode = mkHashCode

  // override def hashCode = {
  //   if(theHashCode == 0) theHashCode = mkHashCode
  //   theHashCode
  // }

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
    val len1 = cpts1.length; val len2 = cpts2.length
    // identities of cpts1
    // val ids1 = new Array[ProcessIdentity](len1); var i = 0
    // while(i < len1){ ids1(i) = cpts1(i).componentProcessIdentity; i += 1 }
    // val ids1 = cpts1.map(_.componentProcessIdentity)
    // require(cpts2.forall(st => 
    //   !ids1.contains(st.componentProcessIdentity) || cpts1.contains(st)))
    // Iterate through cpts2; count the number disjoint from cpts1, recording
    // those disjoint in newC, and check the two agree on common components.
    var i = 0; var count = 0; val newC = new Array[Boolean](len2)
    while(i < len2){
      val cpt2 = cpts2(i); val pid2 = cpt2.componentProcessIdentity; var j = 0
      // search for cpt2 in cpts1
      while(j < len1 && cpts1(j).componentProcessIdentity != pid2) j += 1
      if(j < len1) require(cpts1(j) == cpt2) else{ newC(i) = true; count += 1 }
      i += 1
    }
    // Copy cpts1 and distinct components of cpts2 (s.t. newC(_)) into result.
    val result = new Array[State](len1+count); i = 0
    while(i < len1){ result(i) = cpts1(i); i += 1}
    var j = 0
    while(j < len2){ if(newC(j)){ result(i) = cpts2(j); i += 1 }; j += 1 }
    assert(i == len1+count)
    result
    // cpts1 ++ cpts2.filter(st => !ids1.contains(st.componentProcessIdentity))
  }

  /** Check components in cpts are distinct. */
  def checkDistinct(cpts: Array[State], msg: => String = "") = {
    val len = cpts.length; var i = 0
    while(i < len-1){
      var j = i+1
      while(j < len && cpts(i) != cpts(j)) j += 1
      assert(j == len, showStates(cpts)+" "+msg)
      i += 1
    }
    // for(i <- 0 until cpts.length; j <- i+1 until cpts.length)
    //   assert(cpts(i) != cpts(j), showStates(cpts)+" "+msg)
  }
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

  def componentsList = components.toList

  /** In the case that this was created by extending one view with a component
    * from a secondary view, that secondary view. */
  private var secondaryView: ComponentView = null

  /** In the case that this was created by extending one view with a component
    * from a secondary view, the additional referencing views found in
    * isExtendable. */
  private var referencingViews: Array[ComponentView] = null
  // IMPROVE: would it be enough to store just the non-null elements, to use
  // less memory?

  /** Set the secondary view. */
  def setSecondaryView(sv: ComponentView, rv: Array[ComponentView]) = {
    assert(secondaryView == null); secondaryView = sv; referencingViews = rv
  }

  /** Get the secondary view. */
  def getSecondaryView = secondaryView

  /** Get the referencing views. */
  def getReferencingViews = referencingViews

  /** Maps used in combining with this.  */
  private var map: RemappingMap = servers.remappingMap
  private var nextArg: NextArgMap = null 
  private var otherArgs: OtherArgMap = null

  /** Initialise the above maps. */
  @inline private def initMaps() = {
    nextArg = servers.nextArgMap  // The next fresh parameters
    // Parameters used in components but not the servers
    otherArgs = Array.fill(numTypes)(List[Identity]()); var cix = 0
    // Iterate through params of components
    while(cix < components.length){
      val c = components(cix); val ids = c.ids; val typeMap = c.typeMap
      var i = 0
      while(i < ids.length){
        val f = typeMap(i); val id = ids(i); 
        assert(id <= nextArg(f), this)
        if(id == nextArg(f)){ otherArgs(f) ::= id; nextArg(f) += 1 }
        i += 1
      }
      cix += 1
    }
  }

  /** Create maps suitable for remapping: (1) a RemappingMap that is the
    * identity on servers; (2) the identities of components that are not
    * shared with the servers, indexed by types; (3) a NextArgMap giving the
    * next fresh values not used in servers or components. 
    * 
    * Example:
    * [21[-1](T0) || 22[-1](Null) || 23[-1]()] || [12[1](T0,N0) || 7[0](N0,N1)]
    * gives [-1,-1,-1,-1,-1,-1,-1,-1]; [0,-1,-1,-1]; [List(1, 0);List()]; [2, 1]
    * 
    * Note: these are cloned on each call. 
    */
  def getCombiningMaps: (RemappingMap, OtherArgMap, NextArgMap) = {
    // Profiler.count("getCombiningMaps"+(otherArgs == null))
    if(otherArgs == null) initMaps()
    val map1 = new Array[Array[Int]](numTypes); var t = 0
    while(t < numTypes){ map1(t) = map(t).clone; t += 1 }
    (map1, otherArgs.clone, nextArg.clone)
  }

  /** As getCombiningMaps, except client code must not change the maps
    * returned. */
  def getCombiningMapsImmutable: (RemappingMap, OtherArgMap, NextArgMap) = {
    // Profiler.count("getCombiningMaps"+(otherArgs == null))
    if(otherArgs == null) initMaps()
    (map, otherArgs, nextArg)
  }

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

  override def hashCode = {
    var h = servers.hashCode
    for(st <- components) h = h*73 + st.hashCode
    h
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
