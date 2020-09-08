package ViewAbstraction

import ox.gavin.profiling.Profiler
import scala.math.Ordering.Implicits._ // for sorting list of lists

/** Utility object to apply remapping of parameters in states.  
  * 
  * Some remapping functions take a ParamMap, showing which parameters should
  * be left unchanged.  Each function remaps parameters so that they, and
  * those in the ParamMap if applicable, form an initial segment of the
  * naturals, and their first occurences are in order. */ 
object Remapper{
  // type View = Views.View

  // ======== Memory management

  // ----- RemappingMaps

  /** Max number of values of each type that we need to keep track of in any
    * remapping. */
  val rowSizes = Array.tabulate(numTypes)( t => 
    typeSizes(t) + State.maxParamsOfType(t))
  println("Remapper.rowSizes = "+rowSizes.mkString(", "))

  /** The type of maps recording the values that parameters get remapped to.  
    * map(t)(arg) records the value that arg of type t gets remapped to,
    * or -1 if no value has been allocated yet.  I.e., it represents the
    * mapping
    *  {(t,arg) -> (t, map(t)(arg)) |
    *       0 <= t < numTypes, 0 <= arg < size(t), map(t)(arg) != -1}.
    */
  private type RemappingMap = Array[Array[Int]]

  /** A clear RemappingMap, representing the empty mapping; used as a
    * template for creating more such. */
  private val remappingMapTemplate: RemappingMap = 
    Array.tabulate(numTypes)(t => Array.fill(rowSizes(t))(-1))

  /** A thread-local RemappingMap. */
  private object ThreadLocalRemappingMap extends ThreadLocal[RemappingMap]{
    override def initialValue() = {
      Array.tabulate(numTypes)(t => Array.fill(rowSizes(t))(-1))
    }
  }

  /** A clear RemappingMap, representing the empty mapping, i.e. mapping all
    * entries to -1.  Different calls to this will use the same arrays, so two
    * RemappingMaps created by the same thread should not be in use at the
    * same time. */
  @inline def newRemappingMap: RemappingMap = {
    val map = ThreadLocalRemappingMap.get; var t = 0
    do{
      var i = 0; val len = map(t).length
      do{ map(t)(i) = -1; i += 1 } while(i < len)
      t += 1
    } while(t < numTypes)
    //assert(map.forall(_.forall(_ == -1)))
    map 
  }

  /** Create a RemappingMap corresponding to rho, i.e. the identity map
    * on (t,i) for i <- [0..rho(t), for each t. */
  private def createMap(rho: ParamMap): RemappingMap = {
    val map = newRemappingMap
    for(t <- 0 until numTypes){
      val len = rho(t).length; var i = 0
      while(i < len){ map(t)(i) = i; i += 1 }
      // while(i < rowSizes(t)){ assert(map(t)(i) == -1); i += 1 }
    }
    map
  }

  // ------ NextArgMaps

  /** The type of maps giving the next argument to map a parameter of
    * type t.  The corresponding RemappingMap has domain all
    * parameters (t,i) for i <- [0..nextArg(t)), for each t. */
  private type NextArgMap = Array[Int]

  /** A thread-local NextArgMap. */
  private object ThreadLocalNextArgMap extends ThreadLocal[NextArgMap]{
    override def initialValue() = new Array[Int](numTypes)
  }

  /** Create a new NextArgMap, corresponding to the empty mapping.  Equivalent
    * to new Array[Int](numTypes) */
  @inline private def newNextArgMap: NextArgMap = {
    // We re-use previous maps, to reduce GC churn
    val map = ThreadLocalNextArgMap.get
    for(t <- 0 until numTypes) map(t) = 0
    map
  }

  /** Create a new NextArgMap corresponding to rho. */
  @inline private def createNextArgMap(rho: ParamMap): NextArgMap = {
    val naMap = ThreadLocalNextArgMap.get
    for(i <- 0 until numTypes) naMap(i) = rho(i).length
    naMap
    // rho.map(_.length)
  }

  // ----- Array[StateIndex]

  private type StateIndexArray = Array[StateIndex]

  /** Maximum size of Array[StateIndex] pooled. */
  private val MaxViewSize = 7 // Views.MaxViewSize FIXME

  /** Maximum number of StateIndexArrays to store for each size.  
    * The two remapSplit*Canonical functions use two such.  */
  private val MaxStateIndexPoolSize = 2

  /** Class for managing pool of StateIndexArrays; owned by a single thread. */
  private class StateIndexPool{
    /** pools(i) stores a pool of StateIndexArrays of size i. */
    private val pools = Array.fill(MaxViewSize+1)(
      new Array[StateIndexArray](MaxStateIndexPoolSize))

    /** counts(i) stores the number of StateIndexArrays of size i stored. */
    private val counts = new Array[Int](MaxViewSize+1)

    /** Get a StateIndexArray of size size, maybe reusing a previous one. */
    @inline def get(size: Int): StateIndexArray = 
      if(counts(size) > 0){ counts(size) -= 1; pools(size)(counts(size)) } 
      else new StateIndexArray(size)

    /** Return a for recycling. */
    @inline def put(a: StateIndexArray) = {
      val size = a.length
      if(counts(size) < MaxStateIndexPoolSize){
        pools(size)(counts(size)) = a; counts(size) += 1
      }
      else Profiler.count("StateIndexPool.put fail"+size)
    }
  } // End of StateIndexPool

  /** Thread-local supply of StateIndexArrays. */
  private object ThreadLocalStateIndexPool extends ThreadLocal[StateIndexPool]{
    override def initialValue() = { 
      // Profiler.count("TLSIP.init")
      new StateIndexPool
    }
  }

  /** Get a StateIndexArray of size size, maybe reusing a previous one. */
  @inline private def newStateIndexArray(size: Int): StateIndexArray = 
    ThreadLocalStateIndexPool.get.get(size)

  /** Return a StateIndexArray for recycling. */
  @inline def returnStateIndexArray(a: StateIndexArray) =
    ThreadLocalStateIndexPool.get.put(a)


  // ======================================================= Helper functions

  /** Remap the parameter (t,arg), updating map and arg appropriately. */
  @inline private def remapArg(
    map: RemappingMap, nextArg: NextArgMap, t: Type, arg: Identity)
      : Identity = {
    if(isDistinguished(arg)) arg
    else{
      // assert(arg < SplitFreshVal, arg+": "+map(t).mkString(", ")) 
      val arg1 = map(t)(arg)
      if(arg1 < 0){ map(t)(arg) = nextArg(t); nextArg(t) += 1; nextArg(t)-1 }
      else arg1
    }
  }

  // ------ Remapping a state

  /** Remap the parameters of st, updating map and nextArg. */
  @inline private 
  def remapParams(map: RemappingMap, nextArg: NextArgMap, st: State)
      : Array[Identity] = {
    val cs = st.cs; val ids = st.ids; val len = ids.length; var index = 0
    val remappedParams = State.getIdentityArray(len) 
    val tArray = State.stateTypeMap(cs) // array giving types of ids
    while(index < len){
      remappedParams(index) = remapArg(map, nextArg, tArray(index), ids(index))
      index += 1
    }
    remappedParams
  }

  /** Remap a single state st, updating map and nextArg. */
  @inline private 
  def remapState(map: RemappingMap, nextArg: NextArgMap, st: State): State = {
    val remappedParams = remapParams(map, nextArg, st)
    MyStateMap(st.family, st.cs, remappedParams)// potentially recycles remappedParams
  }

  /** Remap state st, returning its index; also update map and nextArg. */
  @inline private 
  def remapStateToIndex(map: RemappingMap, nextArg: NextArgMap, st: State)
      : StateIndex = {
    val remappedParams = remapParams(map, nextArg, st)
    // Following potentially recycles remappedParams
    MyStateMap.getByIndex(st.family, st.cs, remappedParams)
  }

  // ------ Remapping List[State] or  Views

  /** Remap procs, updating map and nextArg.  */
  @inline private def remapStates(
    map: RemappingMap, nextArg: NextArgMap, procs: List[State]): List[State] = 
    procs.map(st => remapState(map, nextArg, st))

  /** Remap procs, updating map and nextArg.  */
  @inline private def remapStates(
    map: RemappingMap, nextArg: NextArgMap, procs: Array[State]): Array[State] = 
    procs.map(st => remapState(map, nextArg, st))

  @inline private 
  def remapServerStates(map: RemappingMap, nextArg: NextArgMap, ss: ServerStates)
      : ServerStates = 
    ServerStates(remapStates(map, nextArg, ss.servers))

  /** Remap a ComponentView. */
  @inline def remapComponentView(v: ComponentView): ComponentView = {
    val map = newRemappingMap; var nextArg = newNextArgMap
    val servers1 = remapServerStates(map, nextArg, v.servers)
    val principal1 = remapState(map, nextArg, v.principal)
    val others1 = remapStates(map, nextArg, v.others)
    new ComponentView(servers1, principal1, others1)
  }

  def remapView(v: View) = v match{
    case cv: ComponentView => remapComponentView(cv)
  }



  /** Remap v, updating map and nextArg. */
  // @inline private 
  // def remapView(map: RemappingMap, nextArg: NextArgMap, v: View): View = {
  //   val len = v.length; val newView = Views.newView(len) 
  //   for(i <- 0 until len) newView(i) = remapState(map, nextArg, v(i))
  //   newView
  // }

  // /** Remap v, returning representation with StateIndexes, and updating map and
  //   * nextArg. */
  // @inline private 
  // def remapViewToIndexes(map: RemappingMap, nextArg: NextArgMap, v: View)
  //     : Array[StateIndex] = {
  //   val len = v.length; val indexes = newStateIndexArray(len)
  //   for(i <- 0 until len) indexes(i) = remapStateToIndex(map, nextArg, v(i))
  //   indexes
  // }

  // =================================== Permuting states

  /** All permutations of v that preserve that control states are in increasing
    * order. */
  // @inline def viewPerms(v: View): List[View] = 
  //   /* if(v.isEmpty) List(v) else */ viewPermsFrom(v, 0)

  // /** All permutations of v[from..) that are ordered by control state. 
  //   * Pre: from < v.length. */ 
  // private def viewPermsFrom(v: View, from: Int): List[View] = {
  //   val len = v.length
  //   // We avoid recursing on the empty View
  //   if(from == len-1){
  //     val v1 = Views.newView(len); v1(len-1) = v(len-1); List(v1)
  //   }
  //   else{
  //     val h = v(from); val cs = h.cs; var i = from+1
  //     while(i < len && v(i).cs == cs) i += 1
  //     // states v[from..i) all have the same control state.
  //     if(i == len){
  //       if(i+1 == len){ // optimise for this case
  //         val thisPerm = Views.newView(len); thisPerm(i) = v(i); List(thisPerm)
  //       }
  //       else{
  //         var result = List[View]()
  //         for(indexPerm <- indexPerms(i-from)){
  //           val thisPerm = Views.newView(len)
  //           for(j <- 0 until i-from) thisPerm(from+j) = v(from+indexPerm(j))
  //           result ::= thisPerm
  //         }
  //         result
  //       }
  //     } // end of if(i == len)
  //     else{ // optimise in the cases i = from+1, from+2
  //       var tails = viewPermsFrom(v, i)
  //       if(i == from+1){ for(tail <- tails) tail(from) = v(from); tails }
  //       else if(i == from+2){
  //         for(tail <- tails){
  //           val thisPerm = Views.newView(len)
  //           for(j <- i until len) thisPerm(j) = tail(j)
  //           thisPerm(from) = v(from); thisPerm(from+1) = v(from+1)
  //           tails ::= thisPerm; tail(from) = v(from+1); tail(from+1) = v(from)
  //         }
  //         tails
  //       }
  //       else{ // i-from > 2
  //         val myIndexPerms = indexPerms(i-from)
  //         val myIndexPerm0 = myIndexPerms.head
  //         for(tail <- tails){
  //           // re-use tail for first perm
  //           for(j <- 0 until i-from) tail(from+j) = v(from+myIndexPerm0(j))
  //           // Insert all perms of v[from..i) into tail
  //           for(indexPerm <- myIndexPerms.tail){
  //             // assert(indexPerm.length == i-from)
  //             val thisPerm = Views.newView(len)
  //             for(j <- i until len) thisPerm(j) = tail(j)
  //             for(j <- 0 until i-from) thisPerm(from+j) = v(from+indexPerm(j))
  //             // assert((from until len).forall(j => thisPerm(j) != null))
  //             tails ::= thisPerm
  //           }
  //         }
  //         tails
  //       }
  //     }
  //   }
  // }

  /** Array that holds permutations of indices.  indexPerms(j) will hold all
    * permutations of [0..j). */
  // private var indexPerms: Array[Array[Array[Int]]] = null

  // /** Initialise indexPerms.
  //   * @param n the largest number of indices for which to calculate 
  //   * permutations. */
  // def mkIndexPerms(n: Int) = {
  //   indexPerms = new Array[Array[Array[Int]]](n+1)
  //   indexPerms(1) = Array(Array(0))
  //   for(i <- 2 to n){
  //     val prevPerms = indexPerms(i-1)
  //     indexPerms(i) = // array to hold i! perms of [0..i)
  //       new Array[Array[Int]](prevPerms.length*i)
  //     // insert i-1 into each element of prevPerms in all ways
  //     var j = 0
  //     for(perm <- prevPerms; k <- 0 until i){
  //       // Create perm with i-1 in position k; and perm(k) in position i-1
  //       assert(perm.length == i-1)
  //       val thisPerm = new Array[Int](i); perm.copyToArray(thisPerm)
  //       thisPerm(k) = i-1; if(k < i-1) thisPerm(i-1) = perm(k)
  //       indexPerms(i)(j) = thisPerm; j += 1
  //     }
  //   }
  // }

  // ================================= Making canonical forms

  /** Convert components to canonical form, respecting rhoS.  
    * Pre: control states of components are ordered. */
  // def mkCanonical1(components: View, rhoS: ParamMap): (View, Array[Int]) = {
  //   // assert(components.forall(st => st.ids.forall(_ < SplitFreshVal)))
  //   mkCanonicalHelper(components, createMap(rhoS), createNextArgMap(rhoS))
  // }

  // /** Convert servers and components into canonical form.
  //   * @return the canonical form for servers and components, and the number of 
  //   * parameters of each type. */
  // def mkCanonical2(servers: List[State], components: View)
  //     : (List[State], View, Array[Int]) = {
  //   val map = newRemappingMap; var nextArg = newNextArgMap
  //   val newServers = remapStates(map, nextArg, servers)
  //   val (newCpts, newNextArg) = mkCanonicalHelper(components, map, nextArg)
  //   (newServers, newCpts, newNextArg) 
  // }

  // /** Convert components into canonical form, remapping according to map
  //   * and nextArg. */
  // private def mkCanonicalHelper(
  //   components: View, map: RemappingMap, nextArg: NextArgMap)
  //     : (View, Array[Int]) = {
  //   val perms0: List[View] = viewPerms(components)
  //   if(perms0.length == 1){ // optimise for this case
  //     val newView = remapView(map, nextArg, components)
  //     Views.returnView(perms0.head); (newView, nextArg)
  //   }
  //   else{
  //     // Variables to store clones of map and nextArg, to be used with each
  //     // remap of component states, below.  
  //     val newMap = map.map(_.clone) 
  //     var newNextArg: NextArgMap = nextArg.clone
  //     var minPerm: View = remapView(newMap, newNextArg, perms0.head) 
  //     Views.returnView(perms0.head)
  //     for(v <- perms0.tail){
  //       for(i <- 0 until numTypes) newMap(i) = map(i).clone
  //       newNextArg = nextArg.clone
  //       val nextPerm = remapView(newMap, newNextArg, v); Views.returnView(v)
  //       if(Views.compare(nextPerm, minPerm) < 0){ 
  //         Views.returnView(minPerm); minPerm = nextPerm
  //       }
  //       else Views.returnView(nextPerm)
  //     }
  //     (minPerm, newNextArg)
  //   }
  // }

  // =================================== Remapping of splits, in two directions.
  // Used in NewViewExtender

  val SplitFreshVal = State.SplitFreshVal

  /** Remap v0 to its canonical form in terms of StateIndexes, and then remap
    * st, mapping new parameters in the latter to large values, at least
    * SplitFreshVal.
    * @return a pair (minPerm, remappedSts) where minPerm is the canonical
    * form of v0, and remappedSt is st remapped by the same permutation. */
  // def remapSplitCanonical(v0: View, st: State, rhoS: ParamMap)
  //     : (Array[StateIndex], List[StateIndex]) = {
  //   /* Remap v returning its StateIndexes; remap st by the corresponding map,
  //    * and also return its index. IMPROVE: it might be better to remap st only
  //    * for the canonical v1, which means saving the corresponding map. */
  //   @inline def mkSplit(v: View): (Array[StateIndex], StateIndex) = {
  //     val map = createMap(rhoS); val nextArg = createNextArgMap(rhoS)
  //     val ixs = remapViewToIndexes(map, nextArg, v); Views.returnView(v)
  //     for(i <- 0 until numTypes) nextArg(i) = SplitFreshVal
  //     val stix = remapStateToIndex(map, nextArg, st)
  //     assert(stix != 0, s"v = $v; st = $st")
  //     (ixs, stix)
  //   }
  //   // Find min of mkSplit over perms
  //   val perms = viewPerms(v0); val (ixs0, ix0) = mkSplit(perms.head)
  //   // Min perm found so far, and corresponding remapped states
  //   var minPermIxs = ixs0; var minIxs = List(ix0)
  //   for(v <- perms.tail){
  //     val (ixs, ix) = mkSplit(v)
  //     val cmp = compareArrays(ixs, minPermIxs) 
  //     if(cmp == 0){  // v1 == minPerm, value equality!
  //       returnStateIndexArray(ixs); minIxs ::= ix
  //     }
  //     else if(cmp < 0){  // v1 < minPerm 
  //       returnStateIndexArray(minPermIxs); minPermIxs = ixs; minIxs = List(ix)
  //     }
  //     else returnStateIndexArray(ixs)
  //   }
  //   (minPermIxs, minIxs.distinct)
  //   // minPermIxs should be recycled by caller
  // }  

  // /** A thread-local RemappingMap for use in remapSplit1Canonical. */
  // private object ThreadLocalSplitRemappingMaps
  //     extends ThreadLocal[(RemappingMap, Array[List[Identity]])]{
  //   override def initialValue() = {
  //     (new Array[Array[Int]](numTypes), new Array[List[Identity]](numTypes))
  //   }
  // }

  /** Remap v0 to its canonical form, returning representation in terms of
    * StateIndexes; also return ParamMap for variables in remapped v0, and
    * parameters that are new in st (i.e. not in rhoS or v0).
    * @return a tuple (rv, map1, newArgs) where: rv is the remapped
    * version of v0 in terms of StateIndexes; map1 is a map to rename rv back
    * to v0; newArgs gives the new parameters in sts that didn't appear in v0
    * or rhoS. */
  // def remapSplit1Canonical(v0: View, st: State, rhoS: ParamMap)
  //     : (StateIndexArray, Array[Array[Int]], Array[List[Identity]]) = {
  //   // Representation of min value found so far
  //   var ixsMin: StateIndexArray = null
  //   // Map to rename ixsMin back to v, and list of fresh parameters.  Note: the
  //   // former exists concurrently with the ThreadLocalRemappingMap, so needs
  //   // to be distinct.
  //   val (map1, newArgs) = ThreadLocalSplitRemappingMaps.get
  //   for(v <- viewPerms(v0)){ 
  //     val map = createMap(rhoS); val nextArg = createNextArgMap(rhoS)
  //     val ixs = remapViewToIndexes(map, nextArg, v)
  //     Views.returnView(v)
  //     if(ixsMin == null || compareArrays(ixs, ixsMin) < 0){ // ixs < ixsMin
  //       // This is a new min
  //       if(ixsMin != null) returnStateIndexArray(ixsMin)
  //       ixsMin = ixs
  //       // Create map to rename v1 back to v
  //       for(t <- 0 until numTypes){
  //         map1(t) = remappingMapTemplate(t).clone
  //         for(i <- 0 until rowSizes(t)){
  //           val j = map(t)(i); if(j >= 0) map1(t)(j) = i
  //         }
  //       }
  //       // Find parameters of sts not in v0 or rhoS, and hence not in map at this
  //       // point
  //       for(t <- 0 until numTypes) newArgs(t) = List[Identity]()
  //       val ids = st.ids; var index = 0; val n = ids.length
  //       while(index < n){
  //         val id = ids(index); val t = st.typeMap(index); index += 1
  //         if(id >= 0 && map(t)(id) == -1 && !newArgs(t).contains(id))
  //           newArgs(t) ::= id
  //       }
  //     } // end of "This is a new min".
  //     else returnStateIndexArray(ixs)
  //   } // end of for
  //   (ixsMin, map1, newArgs) // ixsMin should be recycled by caller
  // }


}
