package ViewAbstraction
import collection.OpenHashMap
import ox.gavin.profiling.Profiler
import collection.OpenHashSet

/** A component-centric view.
  * @param servers the states of the servers
  * @param components the components, with the principal component state first.
  * 
  * This defines most of the functionality of ComponentViews, excluding those
  * parts that depend upon Concretizations.
  */
abstract class ComponentView0(servers: ServerStates, components: Array[State])
    extends ReducedComponentView(servers, components){

  Profiler.count("ComponentView0") // 179M with lazySetNoJoined.csp!

  def asReducedComponentView = ReducedComponentView(servers, components)

  // Check this is a valid view.
  ComponentView0.checkValid(servers, components)

  /** Identities of components as a bit map. */
  val cptIdsBitMap = IdentitiesBitMap.makeIdsBitMap(components) 

  import FlatArrayMap.FlatArrayMap

  /** For each parameter (t,i), the index of the component that has (t,i) as its
    * identity, or -1 if there is no such. */ 
  private val flatIdsIndexMap: FlatArrayMap[Byte] = 
    FlatArrayMap.from2D(StateArray.makeIdsIndexMap(components))
  // val idsIndexMap: Array[Array[Byte]] = StateArray.makeIdsIndexMap(components)

  /** The index of the component that has (t,i) as its identity, or -1 if there
    * is no such. */ 
  def idsIndexMap(t: Type)(id: Identity) = 
    FlatArrayMap.get(flatIdsIndexMap, t, id)


  /** The component state of this with identity (f,id), or null if there is no
    * such component. */
  def find(f: Family, id: Identity): State = {
    val ix = idsIndexMap(f)(id)
    if(ix < 0) null else components(ix)
  }

  /** The number of components. */ 
  private val cptsLen = components.length

  /** Bit map showing which parameters are in the components, if singleRef. */
  // val cptParamBitMap = newBitMap
  // if(singleRef) 
  //   for(c <- components; (t,p) <- c.processIdentities; if !isDistinguished(p))
  //     cptParamBitMap(t)(p) = true

  /** A bound on the values of each type. */
  private var paramsBound: Array[Int] = null 

  /** A bound on the values of each type. */
  def getParamsBound: Array[Int] = synchronized{
    if(paramsBound == null)
      paramsBound = View.getParamsBound(servers, components)
    paramsBound
  }

  /** Is this representable using the values defined in the script? */
  def representableInScript: Boolean = {
    if(! servers.representableInScript) false
    else{
      var i = 0
      while(i < components.length && components(i).representableInScript) i += 1
      i == components.length
    }
  }

  import ComponentView0._
  /** Object containing the information needed for
    * Transition.mightGiveSufficientUnifs.  This is designed to give better
    * memory behaviour. */
  val mightGiveSufficientUnifsInfo: MightGiveSufficientUnifsInfo = {
    val princFamily = components(0).family
    val cStates = components.map(_.cs) // IMPROVE: remove dups?
    val len = cStates.length
    if(len == 1) new MightGiveSufficientUnifs1(princFamily, cStates(0))
    else if(len == 2) 
      new MightGiveSufficientUnifs2(princFamily, cStates(0), cStates(1))
    else new MightGiveSufficientUnifsN(princFamily, cStates)
  }

  // -------------------------------------------------------

  /** Information about transitions pre -> post for which we have considered
    * induced transitions from this view, with pre.servers = this.servers !=
    * post.servers, the servers do not acquire a new reference, and no
    * component of this changes state in the transition (as the result of a
    * unification).  The set of post.servers for such transitions.
    * 
    * The representation is a bit map.  The ServerStates with index ssIx is
    * stored in entry indexFor(ssIx); maskFor(ssIx) provides an appropriate
    * bit mask.  The array is initialised and extended lazily. Protected by
    * synchronized blocks.  */
  private var doneInducedPostServersBM: Array[Long] = null // new Array[Long](0)
// IMPROVE: under some circumstances it would be better to just store the
// indices in an Array[Int]

  /** The index into doneInducedPostServersBM for a ServersState with index
    * ssIx. */
  @inline private def indexFor(ssIx: Int) = ssIx >> 6 // ssIx / 64

  /** Bit mask to extract the bit for a ServerState with index ssIx. */
  @inline private def maskFor(ssIx: Int) = 1L << (ssIx & 63)

  /** (With singleRef.) Have we previously stored postServers against this?  */
  def containsDoneInduced(postServers: ServerStates): Boolean = {
    // if(ComponentView0.highlightMissing(this))
    //   println(s"$this: containsDoneInduced($postServers); "+
    //     postServers.index+"; "+indexFor(postServers.index))
    containsDoneInducedByIndex(postServers.index)
  }

  /** (With singleRef.) Have we previously stored some postServers with
    * postServers.index == ssIx against this?  */
  @inline def containsDoneInducedByIndex(ssIx: Int): Boolean = synchronized{
    val ix = indexFor(ssIx) 
    doneInducedPostServersBM != null &&
      ix < doneInducedPostServersBM.length &&
      (doneInducedPostServersBM(ix) & maskFor(ssIx)) != 0
  }

  /** Record that we are considering an induced transition with this, with no
    * unification, and whose post-state has postServers.  Return true if this
    * is the first such. */
  def addDoneInduced(postServers: ServerStates): Boolean = synchronized{
    val ssIx = postServers.index; val ix = indexFor(ssIx)
    // if(ComponentView0.highlightMissing(this))
    //   println(s"$this: addDoneInduced($postServers); $ssIx; $ix")
    if(doneInducedPostServersBM == null || 
        ix >= doneInducedPostServersBM.length){
      // Extend doneInducedPostServersBM
      val newBM = new Array[Long](ix+1)
      if(doneInducedPostServersBM != null)
        doneInducedPostServersBM.copyToArray(newBM)
      doneInducedPostServersBM = newBM
    }
    val mask = maskFor(ssIx)
    if((doneInducedPostServersBM(ix) & mask) == 0){
      doneInducedPostServersBM(ix) |= mask; true
    }
    else false
  }

  // -------------------------------------------------------

  // A representation of a map 
  import ServersReducedMap.ReducedMap // = Array[Long]

  /** If singleRef, pairs (post.servers, Remapper.rangeRestrictTo(map,
    * post.servers)) for which we have produced a primary induced transition
    * from this with no unifications.  */
  private val doneInducedPostServersRemaps = 
    if(singleRef && StoreDoneInducedPostServersRemaps)
      new OpenHashSet[ServersReducedMap](initSize = 4, ThresholdRatio = 0.6F)
    else null

  /** Record that this has been used to create an induced transition, with
    * post.servers = servers, result-defining map corresponding to map, and
    * unified components with post-states corresponding to postUnified.  */
  @inline def addDoneInducedPostServersRemaps(
    servers: ServerStates, map: ReducedMap, postUnified: List[State] = null)
      : Boolean = {
    assert(postUnified == null)
    val key = ServersReducedMap(servers, map, postUnified)
    synchronized{ doneInducedPostServersRemaps.add(key) }
  }

  /** Has this been used to create an induced transition, with post.servers =
    * servers, result-defining map corresponding to map, and unified
    * components with post-states corresponding to postUnified?  */
  def containsDoneInducedPostServersRemaps(
    servers: ServerStates, map: ReducedMap, postUnified: List[State] = null)
      : Boolean = {
    assert(postUnified == null)
    val key = ServersReducedMap(servers, map, postUnified)
    synchronized{ doneInducedPostServersRemaps.contains(key) }
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
  private type CrossRefInfo = Array[Array[State]] // List[Array[State]]

  private def showCRI(crossRefs: CrossRefInfo) =
    crossRefs.map(StateArray.show).mkString("; ")

  /** A map storing information about primary induced transitions with no
    * unifications that are currently prevented by condition (b).  This
    * represents the set of tuples (servers, this, map, crossRefs) for
    * crossRefs in conditionBInducedMap(srm), where srm is the
    * ServersReducedMap representing (servers, map).  Inv: for each such
    * mapping, post.servers != this.servers; and for each list in the range,
    * no element of the list is a subset of another.  Protected by
    * synchronized blocks. */
  private var conditionBInducedMap = 
    if(singleRef) 
      new OpenHashMap[ServersReducedMap, Array[CrossRefInfo]](
        initSize = 4, ThresholdRatio = 0.6F)
    else null

  /** Is crossRefs1 a subset of crossRefs2? 
    * 
    * Pre: both are sorted by StateArray.lessThan. */
  @inline private 
  def subset(crossRefs1: CrossRefInfo, crossRefs2: CrossRefInfo): Boolean = {
    import StateArray.lessThan
    val len1 = crossRefs1.length; val len2 = crossRefs2.length
    // IMPROVE
    for(i <- 1 until len1) assert(lessThan(crossRefs1(i-1), crossRefs1(i)))
    for(i <- 1 until len2) assert(lessThan(crossRefs2(i-1), crossRefs2(i)))
    var i1 = 0; var i2 = 0; var ok = true
    // Inv: ok = true if crossRefs1[0..i1) is a subset of crossRefs[0..i2) and
    // false if crossRefs(i1) is not in crossRefs2.  Also no element of
    // crossRefs1[i1..) is in crossRefs[0..i2).
    while(i1 < len1 && ok){
      val cr1 = crossRefs1(i1); i1 += 1
      while(i2 < len2 && lessThan(crossRefs2(i2), cr1)) i2 += 1
      ok = i2 < len2 && crossRefs2(i2) == cr1
    }
/*
    var i1 = 0; var ok = true; val len2 = crossRefs2.length
    while(i1 < crossRefs1.length && ok){
      val cs1 = crossRefs1(i1); i1 += 1
      var i2 = 0 // test if crossRefs2 contains cs1
      // while(i2 < len2 && !sameElements(crossRefs2(i2), cs1)) i2 += 1
      while(i2 < len2 && crossRefs2(i2) != cs1) i2 += 1
      ok = i2 < len2
    }
 */
    // crossRefs1.forall(cs1 => crossRefs2.exists(cs => cs.sameElements(cs1) ))
    //var crs1 = crossRefs1; var ok = true
    // // Inv: ok is true if all elements of crossRefs1 so far are in crossrefs2
    // while(crs1.nonEmpty && ok){
    //   val cs1 = crs1.head; crs1 = crs1.tail
    //   // test if crossRefs2 contains cs1
    //   var crs2 = crossRefs2
    //   while(crs2.nonEmpty && !sameElements(crs2.head, cs1)) crs2 = crs2.tail
    //   ok = crs2.nonEmpty
    // }
    ok
  }
  // IMPROVE.  Maybe keep lists sorted.

  @inline private def sameElements(cr1: Array[State], cr2: Array[State]) = {
    // assert(cr1.length == 2 && cr2.length == 2) 
    cr1(0) == cr2(0) && cr1(1) == cr2(1)
  }

  /** Is there a stored primary induced transition with no unifications that
    * subsumes the transition corresponding to (servers, map, crossRefs)?
    * 
    * Pre: each element of crossRefs must be the value registered in
    * StateArray.  */
  def containsConditionBInduced(
    servers: ServerStates, map: ReducedMap, crossRefs: CrossRefInfo)
      : Boolean = synchronized{
    // assert(crossRefs.forall(cpts => components.eq(StateArray(components))))
    val key = ServersReducedMap(servers, map)
    conditionBInducedMap.get(key) match{
      case Some(crl) =>  // Test if some element of crl is a subset of crossRefs
        var i = 0; val len = crl.length
        while(i < len && !subset(crl(i), crossRefs)) i += 1
        i < len
        // var crossRefsList = crl; var done = false
        // while(crossRefsList.nonEmpty && !done){
        //   val crossRefs1 = crossRefsList.head; crossRefsList = crossRefsList.tail
        //   // If crossRefs1 is a subset of crossRefs, return true
        //   done = subset(crossRefs1, crossRefs)
        // }
        // done
      case None => false
    }
  }

  /** Record that there is a stored primary induced transition with no
    * unifications corresponding to (servers, map, crossRefs)?  Return true if
    * this is a genuine addition, i.e. not subsumed in an existing record
    * (with a subset of the crossRefs).
    *  
    * Pre: each element of crossRefs must be the value registered in
    * StateArray. */
  def addConditionBInduced(
    servers: ServerStates, map: ReducedMap, crossRefs: CrossRefInfo)
      : Boolean = synchronized{
    // assert(crossRefs.forall(cpts => components.eq(StateArray(components))))
    val key = ServersReducedMap(servers, map)
    conditionBInducedMap.get(key) match{
      case Some(crl) => 
        // Find those elements of crl that are not a superset of crossRefs
        var newList = List[CrossRefInfo](); var i = 0
        var foundSubset = false // have we found a subset of crossRefs?
        while(i < crl.length){
          val crossRefs1 = crl(i); i += 1
          if(!subset(crossRefs, crossRefs1)) newList ::= crossRefs1
          foundSubset ||= subset(crossRefs1, crossRefs)
        }
        // Profiler.count(s"addConditionBInduced:"+crl.length)
        // Up to ~150, but mostly below 10.
        // Remove all supersets of crossRefs
        // var newList = List[CrossRefInfo](); var crossRefsList = crl
        // var foundSubset = false // have we found a subset of crossRefs?
        // while(crossRefsList.nonEmpty){
        //   val crossRefs1 = crossRefsList.head; crossRefsList = crossRefsList.tail
        //   if(!subset(crossRefs, crossRefs1)) newList ::= crossRefs1
        //   foundSubset ||= subset(crossRefs1, crossRefs)
        //   // If crossRefs and crossRefs1 are equivalent (permutations), we
        //   // retain the latter.
        // }
        // At present, we should always have !foundSubSet.  
        if(!foundSubset) newList ::= crossRefs
        // else if(false)
        //   println(s"Not added: ${showCRI(crossRefs)}\n${crl.map(showCRI)}")
        conditionBInducedMap.add(key, newList.toArray); !foundSubset

      case None => conditionBInducedMap.add(key, Array(crossRefs)); true
          // += key -> List(crossRefs); true
    }
  }

  /** Clear information about induced transitions.  Used in unit testing. */
  def clearInduced = {
    // if(doneInducedPostServers != null) doneInducedPostServers.clear
    doneInducedPostServersBM = new Array[Long](0)
    // if(conditionBInducedMap != null) conditionBInducedMap.clear()
    if(singleRef) 
      conditionBInducedMap = 
        new OpenHashMap[ServersReducedMap, Array[CrossRefInfo]]
  }

}

// ==================================================================

object ComponentView0{
  /** Check that making a view from servers and components is valid. */
  def checkValid(servers: ServerStates, components: Array[State]) = 
    if(debugging){
      def show = s"($servers, "+StateArray.show(components)+")"
      val cptsLen = components.length; val principal = components(0)
      val len = principal.ids.length;
      if(singleRef){
        if(cptsLen == 2){
          // Check principal has a reference to the other component
          val cPid = components(1).componentProcessIdentity; var i = 0
          while(i < len && principal.processIdentity(i) != cPid) i += 1
          assert(i < len, s"Not a correct ComponentView: $show, ")
          assert(principal.includeParam(i),
            s"Not a correct ComponentView, omitted component included: $show")
        }
        else assert(cptsLen == 1, s"Too many components in ComponentView: $show")
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
              s"Not a correct ComponentView: $show")
          }
          i += 1
        }
        // Check all of others referenced by principal
        var j = 1
        while(j < cptsLen){
          val otherId = components(j).componentProcessIdentity
          var i = 0
          while(i < len && principal.processIdentity(i) != otherId) i += 1
          assert(i < len, s"Not a correct ComponentView: $show")
          assert(principal.includeParam(i),
            s"Not a correct ComponentView, omitted component included: $show")
          j += 1
        }
      }
    }



  /** Object containing the information needed for
    * Transition.mightGiveSufficientUnifs. */
  trait MightGiveSufficientUnifsInfo{
    /** The family of the principal. */
    val princFamily: Family

    /** Does a component have control state cs? */
    def hasControlState(cs: ControlState): Boolean
  }
  // IMPROVE: maybe also include doneInducedPostServersBM here

  /** Implementation of MightGiveSufficientUnifsInfo for one control state. */
  class MightGiveSufficientUnifs1(val princFamily: Family, cs1: ControlState)
      extends MightGiveSufficientUnifsInfo{
    @inline def hasControlState(cs: ControlState) = cs == cs1
  }

  /** Implementation of MightGiveSufficientUnifsInfo for two control states. */
  class MightGiveSufficientUnifs2(
    val princFamily: Family, cs1: ControlState, cs2: ControlState)
      extends MightGiveSufficientUnifsInfo{
    @inline def hasControlState(cs: ControlState) = cs == cs1 || cs == cs2
  }

  /** Implementation of MightGiveSufficientUnifsInfo for arbitrary many control
    * states. */
  class MightGiveSufficientUnifsN(
    val princFamily: Family, controlStates: Array[ControlState])
      extends MightGiveSufficientUnifsInfo{

    private val cptsLen = controlStates.length

    /** Does this have a component with control state cs? */
    @inline def hasControlState(cs: ControlState): Boolean = {
      var j = 0
      while(j < cptsLen && controlStates(j) != cs) j += 1
      j < cptsLen
    }
  }

  // -------------------------------------------------------

  /* Functions used when debugging, to highlight particular views. */

  /** Should we highlight information about v? */
  def highlight(v: ReducedComponentView) = 
    highlightOrigin(v) // || highlightPrev(v)

  /** The view whose origin we are trying to find.  
    * [107(N0) || 109(N0) || 110() || 113() || 119() || 1()] ||
    *   [31(T0,N1,N2,N3) || 10(N1,Null,N2)] */
  private def highlightOrigin(v: ReducedComponentView) = 
    highlightServers(v.servers) && {
      val princ = v.components(0)
      princ.cs == 31 && princ.ids.sameElements(Array(0,1,2,3)) && {
        val second = v.components(1)
        second.cs == 10 // && second.ids.sameElements(Array(1,-1,2))
      }
    }

  /* [36(T0,N1,N2,N0) || 10(N1,N3,N2)]. */
  // def highlightPrevCpts(cpts: Array[State]) = {
  //   val princ = cpts(0)
  //   princ.cs == 36 && princ.ids.sameElements(Array(0,1,2,0)) &&
  //   cpts(1).cs == 10 // && ...
  // }

  // 10(N3,Null,N1)
  // def highlightNext(st: State) = 
  //   st.cs == 10 && st.ids.sameElements(Array(3,-1,1))

  /** The predecessor of the view whose origin we're trying to find. 
    * [137(N0) || 138() || 146(N0) || 147(Null) || 151() || 152()] || 
    *   [46(T0,N1) || 11(N1,N2,N0). */
  // private def highlightPrev(v: ReducedComponentView) = 
  //   highlightServers(v.servers) && highlightPrevCpts(v.components)

  // def highlightPrev(v: Concretization) = 
  //   highlightServers(v.servers) && highlightPrevCpts(v.components)

  /** The servers common to the missing view and the pre-state of the transition
    * that induces it.
    * [107(N0) || 109(N0) || 110() || 113() || 119() || 1()] */
  @inline def highlightServers0(servers: ServerStates) = 
    false && 
    servers(0).cs == 107 && servers(1).cs == 109 && servers(1).ids(0) == 0 && 
    servers(2).cs == 110 && servers(3).cs == 113 && servers(4).cs == 119

  /** The servers for the view under consideration.  */
  def highlightServers(servers: ServerStates) = {
    highlightServers0(servers)//  &&
    // servers(4).cs == 121 && servers(4).ids.sameElements(Array(0,0,1))
  }


}
