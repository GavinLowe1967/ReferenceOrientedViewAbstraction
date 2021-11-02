package ViewAbstraction

import ox.gavin.profiling.Profiler

/** Superclass of views of a system state. */
abstract class View{
  /** This view was created by the extended transition pre -e-> post. */
  private var pre, post: Concretization = null
  private var e: EventInt = -1

  /** The ply on which this was created.  This is only used in assertions. */
  //var ply = Int.MaxValue

  // def setPly(p: Int) = { 
  //   require(ply == Int.MaxValue || ply == p, s"$ply $p"); ply = p 
  // }

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
    if(pre != null) (pre, e, post) 
    else{ 
      val (pre1, cpts, cv, post1, newCpts) = creationIngredients
      (mkExtendedPre(pre1, cpts, cv), e, mkExtendedPost(post1, newCpts))
    }

  def getCreationIngredients = creationIngredients

  /** Record that this view was created by the extended transition 
    * pre1 -e1-> post1. */
  def setCreationInfo(
    pre1: Concretization, e1: EventInt, post1: Concretization)
  = {
    //require(ply == Int.MaxValue || ply == ply1, s"$ply $ply1")
    require(creationIngredients == null && pre == null)
    //require(pre1.ply <= ply1, s"${pre1.ply} $ply1")
    //require(post1.ply <= ply1)
    pre = pre1; e = e1; post = post1;// ply = ply1
  }

  /** Record that this view was created by the extended transition
    * mkExtendedPre(pre1, cpts, cv) -e1-> mkExtendedPost(post1, newCpts).
    */
  def setCreationInfoIndirect(
    pre1: Concretization, cpts: Array[State], cv: ComponentView,
    e1: EventInt, post1: Concretization, newCpts: Array[State]) 
  = {
    // require(ply == Int.MaxValue || ply == ply1, s"$ply $ply1")
    // require(pre == null && creationIngredients == null)
    // require(pre1.ply <= ply1 && cv.ply <= ply1 && post1.ply <= ply1,
    //   s"pre1 = $pre1 \ncv = $cv \npost1 = $post1 \n ply1 = $ply1")
    creationIngredients = (pre1, cpts, cv, post1, newCpts); e = e1; // ply = ply1
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
    val len = principal.ids.length; val cptsLen = components.length
    if(singleRef){
      if(cptsLen == 2){
        // Check principal has a reference to the other component
        val cPid = components(1).componentProcessIdentity; var i = 0
        while(i < len && principal.processIdentity(i) != cPid) i += 1
        assert(i < len, s"Not a correct ComponentView: $this")
        assert(principal.includeParam(i),
          s"Not a correct ComponentView, omitted component included: $this")
      }
      else{ 
        assert(cptsLen == 1, s"Too many components in ComponentView: $this") 
        // Note: principal might have other references here, e.g. resulting
        // from a transition 15(T0,N0,N1) || 7(N0,N1) -getDatum.T0.N0.A->
        // 16(T0,N1) || 7(N0,N1)], where the principal loses the reference to
        // N0.
      }
    } // end of if(singleRef)
    else{
      var i = 1; 
      while(i < len){
        val pid = principal.processIdentity(i)
        if(!isDistinguished(pid._2) && principal.includeParam(i)){
          // Test if there is a component with identity pid
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
        assert(principal.includeParam(i),
          s"Not a correct ComponentView, omitted component included: $this")
        j += 1
      }
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

  /** Bit map showing which parameters are in the components, if singleRef. */
  val cptParamBitMap = newBitMap
  if(singleRef) 
    for(c <- components; (t,p) <- c.processIdentities; if !isDistinguished(p))
      cptParamBitMap(t)(p) = true

  /** A bound on the values of each type. */
  private var paramsBound: Array[Int] = null 

  /** A bound on the values of each type. */
  def getParamsBound: Array[Int] = {
    if(paramsBound == null){
      paramsBound = servers.paramsBound.clone
      for(cpt <- components){
        val pb = cpt.getParamsBound
        for(t <- 0 until numTypes) paramsBound(t) = paramsBound(t) max pb(t)
      }      
    }
    paramsBound
  }


  /** Information about transitions pre -> post for which we have considered
    * induced transitions from this view, with pre.servers = this.servers !=
    * post.servers and with no unification.  The set of post.servers for all
    * such transitions. */
  private val doneInducedPostServers = new BasicHashSet[ServerStates]

  /** Record that we are considering an induced transition with this, with no
    * unification, and whose post-state has postServers.  Return true if this
    * is the first such. */
  def addDoneInduced(postServers: ServerStates): Boolean = 
    doneInducedPostServers.add(postServers)

  // A representation of map |> post.servers
  import ComponentView.ReducedMap // = Array[Long] 

  // Abstractly, ReducedMap plus ServerStates
  import ComponentView.ServersReducedMap 

  /** If singleRef, pairs (post.servers, Remapper.rangeRestrictTo(map,
    * post.servers)) for which we have produced a primary induced transition
    * from this with no unifications.  */
  private val doneInducedPostServersRemaps = 
    if(singleRef) new OpenHashSet[ServersReducedMap] 
    else null

  /** Record that this has been used to create an induced transition, with
    * post.servers = servers, and such that pair._1 is the range restriction
    * of the remapping map to the parameters of servers.  pair._2 is a
    * hashCode for pair._1.  */
  @inline def addDoneInducedPostServersRemaps(
    servers: ServerStates, map: ReducedMap)
      : Boolean = {
    val key = ComponentView.mkServersReducedMap(servers, map)
    doneInducedPostServersRemaps.add(key)
  }

  /** Has this been used to create an induced transition, with post.servers =
    * servers, and such that pair._1 is the range restriction of the remapping
    * map to the parameters of servers.  pair._2 is a hashCode for
    * pair._1.  */
  def containsDoneInducedPostServersRemaps(
    servers: ServerStates, map: ReducedMap)
      : Boolean = {
    val key = ComponentView.mkServersReducedMap(servers, map)
    doneInducedPostServersRemaps.contains(key) 
  }

  // ======

  /* We store information about primary induced transitions with no unifications
   * that are currently prevented by condition (b).  For a transition induced
   * by pre -> post on v, the information can be thought of as a tuple
   * 
   *  (post.servers, v, map |> post.servers, crossRefs)
   * 
   * where crossRefs is the required views for condition (b).  Each tuple is
   * stored in the View object for v.  Each element of crossRefs can be
   * represented by the states of the components (the servers match
   * v.servers), so the set of crossRefs is represented by a value of type
   * CrossRefInfo.  The transition will create a view equivalent to
   * (post.servers, map(v.components))*/

  /** A representation of the views needed for condition (b) of an induced
    * transition: the list of component states. */
  private type CrossRefInfo = List[Array[State]]

  private def showCRI(crossRefs: CrossRefInfo) =
    crossRefs.map(StateArray.show)

  /** A map storing information about primary induced transitions with no
    * unifications that are currently prevented by condition (b).  This
    * represents the set of tuples (servers, this, map, crossRefs) for
    * crossRefs in conditionBInducedMap(srm), where srm is the
    * ServersReducedMap representing (servers, map).  Inv: for each such
    * mapping, post.servers != this.servers; and for each list in the range,
    * no element of the list is a subset of another.  */
  private val conditionBInducedMap = 
    if(singleRef) 
      new scala.collection.mutable.HashMap[ServersReducedMap, List[CrossRefInfo]]
    else null

  /** Is crossRefs1 a subset of crossRefs2? */
  @inline private 
  def subset(crossRefs1: CrossRefInfo, crossRefs2: CrossRefInfo): Boolean = {
    // crossRefs1.forall(cs1 => crossRefs2.exists(cs => cs.sameElements(cs1) ))
    var crs1 = crossRefs1; var ok = true
    // Inv: ok is true if all elements of crossRefs1 so far are in crossrefs2
    while(crs1.nonEmpty && ok){
      val cs1 = crs1.head; crs1 = crs1.tail
      // test if crossRefs2 contains cs1
      var crs2 = crossRefs2
      while(crs2.nonEmpty && !sameElements(crs2.head, cs1)) crs2 = crs2.tail
      ok = crs2.nonEmpty
    }
    ok
  }
  // IMPROVE.  Maybe keep lists sorted.

  @inline private def sameElements(cr1: Array[State], cr2: Array[State]) = {
    // assert(cr1.length == 2 && cr2.length == 2) 
    cr1(0) == cr2(0) && cr1(1) == cr2(1)
  }

  /** Is there a stored primary induced transition with no unifications that
    * subsumes the transition corresponding to (servers, map, crossRefs)? */
  def containsConditionBInduced(
    servers: ServerStates, map: ReducedMap, crossRefs: CrossRefInfo)
      : Boolean = {
    val key = ComponentView.mkServersReducedMap(servers, map)
    conditionBInducedMap.get(key) match{
      case Some(crl) =>
        var crossRefsList = crl; var done = false
        while(crossRefsList.nonEmpty && !done){
          val crossRefs1 = crossRefsList.head; crossRefsList = crossRefsList.tail
          // If crossRefs1 is a subset of crossRefs, return true
          done = subset(crossRefs1, crossRefs)
        }
        done
      case None => false
    }
  }

  /** Record that there is a stored primary induced transition with no
    * unifications corresponding to (servers, map, crossRefs)?  Return true if
    * this is a genuine addition, i.e. not subsumed in an existing record
    * (with a subset of the crossRefs) */
  def addConditionBInduced(
    servers: ServerStates, map: ReducedMap, crossRefs: CrossRefInfo)
      : Boolean = {
    val key = ComponentView.mkServersReducedMap(servers, map)
    conditionBInducedMap.get(key) match{
      case Some(crl) => 
        // Profiler.count(s"addConditionBInduced:"+crl.length)
        // Up to ~150, but mostly below 10.
        // Remove all supersets of crossRefs
        var newList = List[CrossRefInfo](); var crossRefsList = crl
        var foundSubset = false // have we found a subset of crossRefs?
        while(crossRefsList.nonEmpty){
          val crossRefs1 = crossRefsList.head; crossRefsList = crossRefsList.tail
          if(!subset(crossRefs, crossRefs1)) newList ::= crossRefs1
          foundSubset ||= subset(crossRefs1, crossRefs)
          // If crossRefs and crossRefs1 are equivalent (permutations), we
          // retain the latter.
        }
        // At present, we should always have !foundSubSet.  
        if(!foundSubset) newList ::= crossRefs
        else println(s"Not added: ${showCRI(crossRefs)}\n${crl.map(showCRI)}")
        conditionBInducedMap += key -> newList; !foundSubset

      case None => conditionBInducedMap += key -> List(crossRefs); true
    }
  }

  /** Clear information about induced transitions.  Used in unit testing. */
  def clearInduced = {
    if(doneInducedPostServers != null) doneInducedPostServers.clear
    if(conditionBInducedMap != null) conditionBInducedMap.clear 
  }

  // ==========

  override def toString = 
    s"$servers || "+components.mkString("[", " || ", "]") // +s" <$ply>"

  def toString0 = 
    servers.toString0+" || "+
      components.map(_.toString0).mkString("[", " || ", "]") // +s" <$ply>"

  override def equals(that: Any) = {
    if(that != null){
      val cv = that.asInstanceOf[ComponentView]
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
    var h = servers.hashCode*71 
    var i = 0; var n = components.length
    while(i < n){ h = h*71+components(i).hashCode; i += 1 }    
    h 
  }

  override val hashCode = mkHashCode

  /** Ordering on ComponentViews.  Return a value x s.t.: x < 0 if this < that;
    * x == 0 when this == that; x > 0 when this > that. */
  def compare(that: ComponentView) = {
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
}

// ==================================================================

object ComponentView{
  /** Is v1 < v2. */
  def compare(v1: ComponentView, v2: ComponentView): Boolean = v1.compare(v2) < 0

  /** Type representing the range restriction of a RemappingMap.  The
    * representation is described in Remapper.scala. */
  type ReducedMap = Array[Long]  

  /** A class of objects used to key the doneInducedPostServersRemaps mapping in
    * each ComponentView. */
  abstract class ServersReducedMap{
    /** Combine h and l: used in creating hashCodes. */
    @inline protected def combine(h: Int, l: Long) =
      h ^ l.toInt ^ (l >> 32).toInt
  }

  /** A ServersReducedMap corresponding to an empty map. */
  class ServersReducedMap0(val servers: ServerStates)
  extends ServersReducedMap{
    override def equals(that: Any) = that match{
      case srm: ServersReducedMap0 => srm.servers == servers
      case _: ServersReducedMap => false
    }

    override def hashCode = servers.hashCode
  }

  /** A ServersReducedMap whose map is a single Long. */
  class ServersReducedMap1(val servers: ServerStates, val map: Long)
  extends ServersReducedMap{
    override def equals(that: Any) = that match{
      case srm: ServersReducedMap1 => srm.servers == servers && srm.map == map
      case _: ServersReducedMap => false
    }

    override def hashCode = combine(servers.hashCode, map)
  }

  /** A ServersReducedMap whose map contains at least two Longs. */
  class ServersReducedMapN(val servers: ServerStates, val map: ReducedMap)
  extends ServersReducedMap{
    override def equals(that: Any) = that match{
      case srm: ServersReducedMapN => 
        srm.servers == servers && srm.map.sameElements(map)
      case _: ServersReducedMap => false
    }

    override val hashCode = mkHash

    /** Make the hash function. */ 
    private def mkHash = {
      // effectively foldl combine servers.hashCode map
      var h = servers.hashCode; var i = 0
      while(i < map.length){ h = combine(h, map(i)); i += 1 }
      h
    }
  }

  // IMPROVE: it might be worth having a special case for N=2

  def mkServersReducedMap(servers: ServerStates, map: ReducedMap)
  : ServersReducedMap =
    if(map.isEmpty) new ServersReducedMap0(servers)
    else if(map.length == 1) new ServersReducedMap1(servers, map(0))
    else new ServersReducedMapN(servers, map)

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
          if(st1 != null){
            val v = new ComponentView(servers, Array(princ, st1))//; v.setPly(ply)
            result ::= v
          }
          else otherRef = true
          // println(s"getViewOf: omitting View for ${princIds(i)}")
        }
        i += 1
      }
      // if(result.length > 1) println(s"getViewOf: $result")
      if(result.nonEmpty || otherRef) result 
      // If all the refs from newPrinc are distinguished or omitted, we need
      // to include the singleton view.
      else{
        val v = new ComponentView(servers, Array(princ)) // ; v.setPly(ply)
        List(v)
      }
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
      val v = new ComponentView(servers, components1) // ; v.setPly(ply)
      List(v)
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

  /** The ply on which this was created. */
  //var ply = Int.MaxValue

  //def setPly(p: Int) = { assert(ply == Int.MaxValue); ply = p }

  /** Set the secondary view. */
  def setSecondaryView(sv: ComponentView, rv: Array[ComponentView]) 
  = {
    //require(ply == Int.MaxValue, s"$ply $ply1")
    require(secondaryView == null || secondaryView == sv,
    s"this = $this\nsecondaryView = $secondaryView\nsv = $sv")
    require(sv != null)
    //require(sv.ply < ply1, s"$sv ${sv.ply} $ply1 ")
    //require(rv == null || rv.forall(c => c == null )) // || c.ply < ply1  ), 
      // rv.filter(_ != null).map(_.ply).mkString(","))
    secondaryView = sv; referencingViews = rv //; ply = ply1
  }

  /** Get the secondary view. */
  def getSecondaryView = secondaryView

  /** Get the referencing views. */
  def getReferencingViews = referencingViews

  // =========== Combining maps

  /** Maps used in combining with this.  */
  private var map: RemappingMap = servers.remappingMap // (getParamsBound)
  // Note: map is null if servers is not normalised. 
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
/*
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
 */

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
    val typeMap = state.typeMap; val ids = state.ids
    val len = ids.length; var i = 0
    while(i < len){
      val f = typeMap(i); nextArg(f) = nextArg(f) max (ids(i)+1); i += 1
    }
  }

  override def toString = 
    s"$servers || ${components.mkString("[", " || ", "]")}" // +s" <$ply>"

  def toString0 = 
    servers.toString0+" || "+
      components.map(_.toString0).mkString("[", " || ", "]") // +s" <$ply>"

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
    // c.setPly(cv.ply); 
    c
  }


}
