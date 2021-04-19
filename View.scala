package ViewAbstraction

import ox.gavin.profiling.Profiler

/** Superclass of views of a system state. */
abstract class View{
  /** This view was created by the extended transition pre -e-> post. */
  private var pre, post: Concretization = null
  private var e: EventInt = -1

  /** The ply on which this was created.  This is only used in assertions. */
  var ply = Int.MaxValue

  def setPly(p: Int) = { 
    require(ply == Int.MaxValue || ply == p, s"$ply $p"); ply = p 
  }

  /** Ingredients for making an extended transition.  If this contains a tuple
    * (pre1, cpts, cv, post1, newCpts) then this was created by the extended
    * transition 
    * mkExtendedPre(pre1, cpts, cv) -e1-> mkExtendedPost(post1, newCpts). 
    * We lazily avoid creating these concretizations until needed. */ 
  private var creationIngredients: 
      (Concretization, Array[State], ComponentView, Concretization, Array[State])
  = null

  /** Get the creation information for this. */
  def getCreationInfo: (Concretization, EventInt, Concretization) = 
    if(pre != null){ /* println("old style");*/  (pre, e, post) }
    else{ 
      // println("new style")
      val (pre1, cpts, cv, post1, newCpts) = creationIngredients
      (mkExtendedPre(pre1, cpts, cv), e, mkExtendedPost(post1, newCpts))
    }

  /** Record that this view was created by the extended transition 
    * pre1 -e1-> post1. */
  def setCreationInfo(
    pre1: Concretization, e1: EventInt, post1: Concretization, ply1: Int)
  = {
    require(ply == Int.MaxValue || ply == ply1, s"$ply $ply1")
    require(creationIngredients == null && pre == null)
    require(pre1.ply <= ply1, s"${pre1.ply} $ply1")
    require(post1.ply <= ply1)
    pre = pre1; e = e1; post = post1; ply = ply1
  }

  /** Record that this view was created by the extended transition
    * mkExtendedPre(pre1, cpts, cv) -e1-> mkExtendedPost(post1, newCpts).
    */
  def setCreationInfoIndirect(
    pre1: Concretization, cpts: Array[State], cv: ComponentView,
    e1: EventInt, post1: Concretization, newCpts: Array[State], ply1: Int) 
  = {
    require(ply == Int.MaxValue || ply == ply1, s"$ply $ply1")
    require(pre == null && creationIngredients == null)
    require(pre1.ply <= ply1 && cv.ply <= ply1 && post1.ply <= ply1,
      s"pre1 = $pre1 \ncv = $cv \npost1 = $post1 \n ply1 = $ply1")
    creationIngredients = (pre1, cpts, cv, post1, newCpts); e = e1; ply = ply1
  }

  /** Make the extended pre-state by extending pre1 with cpts, and setting cv as
    * the secondary view. */
  private def mkExtendedPre(
    pre1: Concretization, cpts: Array[State], cv: ComponentView)
      : Concretization = {
    val extendedPre = new Concretization(pre1.servers,
      View.union(pre1.components, cpts))
    extendedPre.setSecondaryView(cv, null, ply)
    extendedPre
  }

  /** Make the extended post-state by extending post1 with newCpts. */
  private def mkExtendedPost(post1: Concretization, newCpts: Array[State]) = 
    new Concretization(post1.servers, View.union(post1.components, newCpts))
}

// =======================================================

/** A component-centric view.
  * @param servers the states of the servers
  * @param components the components, with the principal component state first.
  */
class ComponentView(val servers: ServerStates, val components: Array[State])
    extends View{

  def this(servers: ServerStates, principal: State, others: Array[State]){
    this(servers, principal +: others)
  }

  /** The principal component. */
  def principal = components(0)

  /** Check all components referenced by principal are included, and no more. */
  // IMRPOVE: this is moderately expensive
  @noinline private def checkValid = if(debugging){ 
    val len = principal.ids.length; val cptsLen = components.length; var i = 1
    val includeInfo = State.getIncludeInfo(principal.cs)
    while(i < len){
      val pid = principal.processIdentity(i)
      if(!isDistinguished(pid._2) && (includeInfo == null || includeInfo(i))){
        // Test if otherPids.contains(pid)
        var j = 1
        while(j < cptsLen && components(j).componentProcessIdentity != pid) 
          j += 1
        assert(j < cptsLen || pid == principal.componentProcessIdentity,
          s"Not a correct ComponentView: $this")
      }
      i += 1
    }
    // Check all of others referenced by principal
    var j = 1
    while(j < cptsLen){
      val otherId = components(j).componentProcessIdentity 
      var i = 0
      while(i < len && principal.processIdentity(i) != otherId) i += 1
      assert(i < len, s"Not a correct ComponentView: $this")
      assert(includeInfo == null || includeInfo(i), 
        s"Not a correct ComponentView, omitted component included: $this")
      j += 1
    }
  }

  checkValid

  /** Is this representable using the values defined in the script? */
  def representableInScript: Boolean = {
    if(! servers.representableInScript) false
    else{
      var i = 0
      while(i < components.length && components(i).representableInScript) i += 1
      i == components.length
    }
  }

  override def toString = 
    s"$servers || "+components.mkString("[", " || ", "]")+s" <$ply>"

  def toString0 = 
    servers.toString0+" || "+
      components.map(_.toString0).mkString("[", " || ", "]")+s" <$ply>"

  override def equals(that: Any) = that match{
    case cv: ComponentView => 
      servers == cv.servers && components.sameElements(cv.components)
  }

  /** Create hash code. */
  @inline private def mkHashCode = {
    var h = servers.hashCode*71 
    var i = 0; var n = components.length
    while(i < n){ h = h*71+components(i).hashCode; i += 1 }    
    h 
  }

  override val hashCode = mkHashCode
}


// =======================================================

/** Companion object. */
object View{
  /** All components referenced by principal in states, including itself. */
  def referencedStates(principal: State, states: Array[State]): Array[State] = {
    val len = principal.ids.length
    val refed = new Array[State](len); refed(0) = principal
    for(i <- 1 until len){
      val thisId = principal.ids(i)
      val matches = states.filter(_.ids(0) == thisId)
      assert(matches.length == 1)
      refed(i) = matches(0)
    }
    refed
  }

  def showStates(states: Array[State]) = 
    states.map(_.toString0).mkString("[", " || ", "]")

  def show(servers: ServerStates, states: Array[State]) =
    servers.toString+" || "+showStates(states)

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
    j == cpts1.length 
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
  private def getViewOf(princ: State): ComponentView = {
    val princIds = princ.processIdentities; val len = princIds.length
    var components1 = new Array[State](len); components1(0) = princ
    val includeInfo = State.getIncludeInfo(princ.cs)
    // Other components to be included in the ComponentView: those referenced 
    // by princ
    var i = 1; var j = 1
    // We have filled components1[0..j) from princIds[0..i)
    while(i < len){
      val pid = princIds(i)
      if(!isDistinguished(pid._2) && (includeInfo == null || includeInfo(i))){
        // Test if this is the first occurrence of pid
        var k = 0; while(k < i && princIds(k) != pid) k += 1
        if(k == i){
          // Find pid in components
          var k = 1
          while(components(k).componentProcessIdentity != pid) k += 1
          components1(j) = components(k); j += 1; k += 1
        }
        // else println("Repeated parameter "+princ)
      }
      i += 1
    }
    if(j < len){
      // Some distinguished, repeated or omitted parameters; trim unfilled slots.
      val nc = new Array[State](j); var k = 0
      while(k < j){ nc(k) = components1(k); k += 1 }
      components1 = nc
    }
    if(debugging){ // testing against previous version IMPROVE
      // val components1X = components.tail.filter{cpt =>
      val components1X = 
        components.filter{ cpt =>
          val (f,id) = cpt.componentProcessIdentity;
          (1 until princIds.length).exists{j =>
            princIds(j) == (f,id) && (includeInfo == null || includeInfo(j))}
        }
      val components2t = components1.tail
      assert(components1X.sameElements(components2t) ||
        components1X.length == components2t.length &&
        components1X.forall(st => components2t.contains(st)),
        s"this = $this\nprinc = $princ"+
        "\ncomponents1X = "+components1X.map(_.toString).mkString("[",", ","]")+
          "\ncomponents1 = "+components1.map(_.toString).mkString("[",", ","]"))
    }
    val v = new ComponentView(servers, components1)
    v.setPly(ply)
    v
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

  /** The ply on which this was created. */
  var ply = Int.MaxValue

  def setPly(p: Int) = { assert(ply == Int.MaxValue); ply = p }

  /** Set the secondary view. */
  def setSecondaryView(sv: ComponentView, rv: Array[ComponentView], ply1: Int) 
  = {
    require(ply == Int.MaxValue, s"$ply $ply1")
    require(secondaryView == null || secondaryView == sv,
    s"this = $this\nsecondaryView = $secondaryView\nsv = $sv")
    require(sv != null)
    require(sv.ply < ply1, s"$sv ${sv.ply} $ply1 ")
    require(rv == null || rv.forall(c => c == null || c.ply < ply1), 
      rv.filter(_ != null).map(_.ply).mkString(","))
    secondaryView = sv; referencingViews = rv; ply = ply1
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
    if(otherArgs == null) initMaps()
    val map1 = new Array[Array[Int]](numTypes); var t = 0
    while(t < numTypes){ map1(t) = map(t).clone; t += 1 }
    (map1, otherArgs.clone, nextArg.clone)
  }

  /** As getCombiningMaps, except client code must not change the maps
    * returned. */
  def getCombiningMapsImmutable: (RemappingMap, OtherArgMap, NextArgMap) = {
    if(otherArgs == null) initMaps()
    (map, otherArgs, nextArg)
  }

  /** Get a (fresh) NextArgMap. */
  def getNextArgMap: NextArgMap = {
    if(otherArgs == null) initMaps()
    nextArg.clone
  }

  /** Update nextArg, so entries are greater than all identities in this. */
  def updateNextArgMap(nextArg: NextArgMap) = {
    var states = servers.servers
    while(states.nonEmpty){
      updateNextArgMapFrom(states.head, nextArg); states = states.tail
    }
    var i = 0
    while(i < components.length){
      updateNextArgMapFrom(components(i), nextArg); i += 1
    }
  }

  /** Update nextArg so entries are greater than identities in state. */
  @inline private def updateNextArgMapFrom(state: State, nextArg: NextArgMap) = {
    // val pids = state.processIdentities
    val typeMap = state.typeMap; val ids = state.ids
    val len = ids.length; var i = 0
    while(i < len){
      // val (f,id) = pids(i); 
      val f = typeMap(i); val id = ids(i)
      nextArg(f) = nextArg(f) max (id+1); 
      i += 1
    }
  }

  override def toString = 
    s"$servers || ${components.mkString("[", " || ", "]")}"+s" <$ply>"

  def toString0 = 
    servers.toString0+" || "+
      components.map(_.toString0).mkString("[", " || ", "]")+s" <$ply>"

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
  def apply(cv: ComponentView) = {
    val c = new Concretization(cv.servers, cv.components)
    // cv.principal +: cv.others)
    c.setPly(cv.ply); c
  }

  def apply(servers: ServerStates, principal: State, others: Array[State]) =
    new Concretization(servers, principal +: others)


}
