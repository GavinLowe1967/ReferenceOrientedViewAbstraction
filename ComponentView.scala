package ViewAbstraction

/** A component-centric view.
  * @param servers the states of the servers
  * @param components the components, with the principal component state first.
  * 
  * This extends ComponentView0 with information related to debugging. 
  */
class ComponentView(servers: ServerStates, components: Array[State])
    extends ComponentView0(servers, components){

  def this(servers: ServerStates, principal: State, others: Array[State]) = {
    this(servers, principal +: others)
  }

  /** This view was created by the extended transition pre -e-> post. */
  private var pre, post: Concretization = null
  private var e: EventInt = -1

  /** Ingredients for making an extended transition.  If this contains a tuple
    * (pre1, cpts, cv, post1, newCpts) then this was created by the extended
    * transition 
    * mkExtendedPre(pre1, cpts, cv) -e1-> mkExtendedPost(post1, newCpts). 
    * We lazily avoid creating these concretizations until needed. */ 
  private var creationIngredients: 
      (Concretization, Array[State], ComponentView, Concretization, Array[State])
  = null

  /** Get the creation information for this. */
  def getCreationInfo: (Concretization, EventInt, Concretization) = synchronized{
    if(pre != null) (pre, e, post) 
    else{ 
      val (pre1, cpts, cv, post1, newCpts) = creationIngredients
      (mkExtendedPre(pre1, cpts, cv), e, mkExtendedPost(post1, newCpts))
    }
  }

  def getCreationIngredients = synchronized{ creationIngredients }

  /** Record that this view was created by the extended transition 
    * pre1 -e1-> post1. */
  def setCreationInfo(pre1: Concretization, e1: EventInt, post1: Concretization)
  = synchronized{
    require(creationIngredients == null && pre == null)
    pre = pre1; e = e1; post = post1
  }

  /** Record that this view was created by the extended transition
    * mkExtendedPre(pre1, cpts, cv) -e1-> mkExtendedPost(post1, newCpts).
    */
  def setCreationInfoIndirect(
    pre1: Concretization, cpts: Array[State], cv: ComponentView,
    e1: EventInt, post1: Concretization, newCpts: Array[State]) 
  = synchronized{
    creationIngredients = (pre1, cpts, cv, post1, newCpts); e = e1
  }

  /** Make the extended pre-state by extending pre1 with cpts, and setting cv as
    * the secondary view. */
  private def mkExtendedPre(
    pre1: Concretization, cpts: Array[State], cv: ComponentView)
      : Concretization = {
    val extendedPre = new Concretization(pre1.servers,
      StateArray.union(pre1.components, cpts))
    extendedPre.setSecondaryView(cv, null)
    extendedPre
  }

  /** Make the extended post-state by extending post1 with newCpts. */
  private def mkExtendedPost(post1: Concretization, newCpts: Array[State]) = 
    new Concretization(post1.servers, 
      StateArray.union(post1.components, newCpts))

  def showCreationInfo: String = creationIngredients match{
    case (pre1, cpts, cv, post1, newCpts) => s"induced by $pre1 -> $post1 on $cv"
    case null => s"produced by $pre -> $post"
  }

  /** Was this induced by a transition from cv1?  Used in trying to understand
    * why so many induced transitions are redundant. */
  def inducedFrom(cv1: ComponentView) = 
    creationIngredients != null && creationIngredients._3 == cv1
}

// ==================================================================

object ComponentView{
  /** Is v1 < v2. */
  def compare(v1: ComponentView, v2: ComponentView): Boolean = v1.compare(v2) < 0

  /** Create a ComponentView from a ReducedComponentView. */
  def fromReducedComponentView(v: ReducedComponentView) = 
    new ComponentView(v.servers, v.components)
}

// =======================================================

/** A concretization. */
class Concretization(val servers: ServerStates, val components: Array[State]){ 

  /** Make ComponentView(s) from this, with components(0) as the principal
    * component.  NOTE: not in canonical form (needs remapping). */
  def toComponentView: List[ComponentView] = getViewOf(components(0))

  /** Get the view(s) of this with princ as principal component.  Pre: if not
    * singleRef then this includes all the components referenced by princ. */
  private def getViewOf(princ: State): List[ComponentView] = {
    val princIds = princ.processIdentities; val len = princIds.length
    val includeInfo = State.getIncludeInfo(princ.cs)

    // Should pids(i) be included?
    @inline def include(i: Int) = {
      val pid = princIds(i)
      if(!isDistinguished(pid._2) && (includeInfo == null || includeInfo(i))){
        // Test if this is the first occurrence of pid
        var k = 0; while(k < i && princIds(k) != pid) k += 1
        k == i
      }
      else false
    }

    if(singleRef){
      var result = List[ComponentView](); var i = 1; var otherRef = false
      // otherRef is set to true if there is an included reference to a
      // component not present in this view.
      while(i < len){
        if(include(i)){
          val st1 = StateArray.find(princIds(i), components)
          if(st1 != null)
            result ::= new ComponentView(servers, Array(princ, st1))
          else otherRef = true
        }
        i += 1
      }
      if(result.nonEmpty || otherRef) result 
      // If all the refs from newPrinc are distinguished or omitted, we need
      // to include the singleton view.
      else List( new ComponentView(servers, Array(princ)) )
    }
    else{
      var components1 = new Array[State](len); components1(0) = princ
      // Other components to be included in the ComponentView: those referenced
      // by princ
      var i = 1; var j = 1
      // We have filled components1[0..j) from princIds[0..i)
      while(i < len){
        if(include(i)){          // Find princIds(i) in components
          components1(j) = StateArray.find(princIds(i), components); j += 1
        }
        i += 1
      }
      if(j < len){
        // Some distinguished, repeated or omitted parameters; trim unfilled
        // slots.
        val nc = new Array[State](j); var k = 0
        while(k < j){ nc(k) = components1(k); k += 1 }
        components1 = nc
      }
      List( new ComponentView(servers, components1) )
    }
  }

  def componentsList = components.toList

  /** Does this have the same component process identities as that? */
  def sameComponentPids(that: Concretization) = {
    val thatCpts = that.components; val length = components.length
    if(thatCpts.length != length) false
    else{
      var i = 0
      while(i < length && thatCpts(i).family == components(i).family && 
        thatCpts(i).ids(0) == components(i).ids(0))
          i += 1
      i == length
    }
  }

  /** Identities of components. */
// IMPROVE: replace by cptIdsBitMap
  val cptIds = components.map(_.componentProcessIdentity)

  /** Identities of components as a bit map. */
  val cptIdsBitMap = StateArray.makeIdsBitMap(components)
// IMPROVE: do we need above given idsIndexMap?

  /** Does this have a component with id (f,id)? */
  def hasPid(f: Family, id: Identity) = cptIdsBitMap(f)(id)

  /** For each parameter (t,i), the index of the component that has (t,i) as its
    * identity, or -1 if there is no such. */ 
  val idsIndexMap: Array[Array[Int]] = StateArray.makeIdsIndexMap(components)

  /** The component state of this with identity (f,id), or null if there is no
    * such component. */
  // def find(f: Family, id: Identity): State = {
  //   val ix = idsIndexMap(f)(id)
  //   if(ix < 0) null else components(ix)
  // }

  /** For each (t,i), the indices of the components c such that (t,i) is a
    * reference of c but not its identity. */
  val refsIndexMap: Array[Array[List[Int]]] =
    StateArray.makeRefsIndexMap(components)

  /** A bound on the values of each type.  IMPROVE: maybe store this. */
  def getParamsBound: Array[Int] = View.getParamsBound(servers, components)

  // ============= Debugging info

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
  def setSecondaryView(sv: ComponentView, rv: Array[ComponentView]) = synchronized{
    require(sv != null && (secondaryView == null || secondaryView == sv),
    s"this = $this\nsecondaryView = $secondaryView\nsv = $sv")
    secondaryView = sv; referencingViews = rv 
  }

  /** Get the secondary view. */
  def getSecondaryView = synchronized{ secondaryView }

  /** Get the referencing views. */
  def getReferencingViews = synchronized{ referencingViews }

  // =========== Combining maps

  /** Maps used in combining with this.  */
  private var map: RemappingMap = servers.remappingMap 
  // Note: map is null if servers is not normalised. 
  private var nextArg: NextArgMap = null 
  private var otherArgs: OtherArgMap = null

  /** Initialise the above maps.  Pre: this is normalised; this won't always
    * hold if this is the post of a transition. */
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

  /** Initialise nextArg.  This does not assume servers are normalised. */
  @inline private def initNextArgMap = {
    nextArg = servers.nextArgMap1; var cix = 0
    // Iterate through params of components
    while(cix < components.length){
      val c = components(cix); val ids = c.ids; val typeMap = c.typeMap
      var i = 0
      while(i < ids.length){
        val f = typeMap(i); nextArg(f) = nextArg(f) max ids(i); i += 1
      }
      cix += 1
    }
  }

  /** Get a (fresh) NextArgMap. */
  def getNextArgMap: NextArgMap = synchronized{
    if(otherArgs == null) initMaps()
    nextArg.clone
  }

  /** Update nextArgMap, so entries are greater than all identities in this. */
  def updateNextArgMap(nextArgMap: NextArgMap) = synchronized{
    if(nextArg == null) initNextArgMap
    var f = 0
    while(f < numTypes){
      nextArgMap(f) = nextArgMap(f) max nextArg(f); f += 1
    }
  }

  /** Update nextArg so entries are greater than identities in state. */
  @inline private def updateNextArgMapFrom(state: State, nextArg: NextArgMap) = {
    val paramsBound = state.getParamsBound; var f = 0
    while(f < numTypes){ nextArg(f) = nextArg(f) max paramsBound(f); f += 1 }
  }

  /** Bit map showing which parameters are in this, if singleRef. */
  val paramsBitMap: BitMap = 
    if(singleRef){
      val pbm = newBitMap
      for(c <- components++servers.servers; (t,p) <- c.processIdentities;
          if !isDistinguished(p))
        pbm(t)(p) = true
      pbm
    }
    else null 

  /** All parameters of components, indexed by type.  Initialised by first call
    * of getAllParams. */
  private var allParams: Array[List[Identity]] = null

  /** All parameters of components, indexed by type. */
  def getAllParams: Array[List[Identity]] = synchronized{
    // assert(singleRef && newEffectOn) -- or also from test
    if(allParams == null){
      allParams = Array.fill(numTypes)(List[Identity]()); var f = 0
      while(f < numFamilies){
        var i = 0; val len = paramsBitMap(f).size
        while(i < len){ if(paramsBitMap(f)(i)) allParams(f) ::= i; i += 1 }
        f += 1
      }
    }
    allParams
  }

  override def toString = 
    s"$servers || ${components.mkString("[", " || ", "]")}"

  def toString0 = 
    servers.toString0+" || "+
      components.map(_.toString0).mkString("[", " || ", "]")

  /** A new concretization, extending this with component newState. */
  def extend(newState: State): Concretization =
    new Concretization(servers, components :+ newState)

  override def equals(that: Any) = that match{
    case c: Concretization => 
      servers == c.servers && components.sameElements(c.components)
  }

  def matches(cv: ComponentView) = 
    servers == cv.servers && components.sameElements(cv.components)

  override def hashCode = {
    var h = servers.hashCode
    for(st <- components) h = h*73 + st.hashCode
    h
  }
} // end of class Concretization

// =======================================================

object Concretization{
  /** Make a concretization from cv. */
  def apply(cv: ComponentView) = new Concretization(cv.servers, cv.components)
}
