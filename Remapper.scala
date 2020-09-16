package ViewAbstraction

import ox.gavin.profiling.Profiler
import scala.math.Ordering.Implicits._ // for sorting list of lists
import scala.collection.mutable.ArrayBuffer

/** Utility object to apply remapping of parameters in states.  
  * 
  * Some remapping functions take a ParamMap, showing which parameters should
  * be left unchanged.  Each function remaps parameters so that they, and
  * those in the ParamMap if applicable, form an initial segment of the
  * naturals, and their first occurences are in order. */ 
object Remapper{

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
  private type RemappingMap = Array[Array[Identity]]

  def showRemappingMap(map: RemappingMap) = 
    map.map(_.mkString("[",",","]")).mkString("; ")

  /** A clear RemappingMap, representing the empty mapping; used as a
    * template for creating more such. */
  // private val remappingMapTemplate: RemappingMap = 
  //   Array.tabulate(numTypes)(t => Array.fill(rowSizes(t))(-1))

  /** A thread-local RemappingMap. */
  // private object ThreadLocalRemappingMap extends ThreadLocal[RemappingMap]{
  //   override def initialValue() = {
  //     Array.tabulate(numTypes)(t => Array.fill(rowSizes(t))(-1))
  //   }
  // }

  // IMPROVE: reinstate pools

  /** A clear RemappingMap, representing the empty mapping, i.e. mapping all
    * entries to -1.  Different calls to this will use the same arrays, so two
    * RemappingMaps created by the same thread should not be in use at the
    * same time. */
  @inline def newRemappingMap: RemappingMap = {
    Array.tabulate(numTypes)(t => Array.fill(rowSizes(t))(-1))
    // val map = ThreadLocalRemappingMap.get;
    // var t = 0
    // do{
    //   var i = 0; val len = map(t).length
    //   do{ map(t)(i) = -1; i += 1 } while(i < len)
    //   t += 1
    // } while(t < numTypes)
    // //assert(map.forall(_.forall(_ == -1)))
    // map 
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

  /** Produce a (deep) clone of map. */
  private def cloneMap(map: RemappingMap): RemappingMap = {
    val map1 = Array.tabulate(numTypes)(t => new Array[Int](rowSizes(t)))
    // val map1 = ThreadLocalRemappingMap.get
    for(t <- 0 until numTypes; i <- 0 until rowSizes(t)) 
      map1(t)(i) = map(t)(i)
    map1
  }

  /** Produce a new RemappingMap, extending map0 so (f,id) maps to id1.
    * Note: the resulting map shares some entries with map0, so neither should 
    * be mutated. */
  private def extendMap(
    map0: RemappingMap, f: Family, id: Identity, id1: Identity)
      : RemappingMap = 
    Array.tabulate(numTypes)(t =>
      if(t != f) map0(t) 
      else{ val newRow = map0(f).clone; newRow(id) = id1; newRow }
    )

  // ------ NextArgMaps

  /** The type of maps giving the next argument to map a parameter of
    * type t.  The corresponding RemappingMap has domain all
    * parameters (t,i) for i <- [0..nextArg(t)), for each t. */
  type NextArgMap = Array[Int]

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

  /** A list, for each type, of non-fresh values that a particular parameter can
    * be mapped to. */
  type OtherArgMap = Array[List[Identity]]

  /** Create maps suitable for remapping: (1) a RemappingMap that is the
    * identity on servers; (2) the identities of components that are not
    * shared with the servers, indexed by types; (3) a NextArgMap giving the
    * next fresh values not used in servers or components. */
  def createMaps(servers: ServerStates, components: Array[State])
      : (RemappingMap, OtherArgMap, NextArgMap) = {

    val rhoS = servers.rhoS; val map0 = createMap(rhoS)
    val serverIds = servers.serverIds
    // The next fresh parameters
    val nextArg: NextArgMap = createNextArgMap(rhoS)
    // Parameters used in v1 but not the servers
    val otherArgs = Array.fill(numTypes)(List[Identity]())
    for(c <- components; i <- 0 until c.ids.length){
      val f = c.typeMap(i); val id = c.ids(i)
      if(!serverIds(f).contains(id) && !otherArgs(f).contains(id)) //IMPROVE
        otherArgs(f) ::= id; nextArg(f) = nextArg(f) max (id+1)
    }
    (map0, otherArgs, nextArg)
  }

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

  // =================== Remapping views

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

  /** Apply map to cpt. 
    * Pre: map is defined on all parameters of cpt. */
  def applyRemappingToState(map: RemappingMap, cpt: State): State = {
    val typeMap = cpt.typeMap; val ids = cpt.ids
    val newIds = Array.tabulate(ids.length){i =>
      val id = ids(i); 
      if(isDistinguished(id)) id 
      else{ val newId = map(typeMap(i))(id); assert(newId >= 0); newId }
    }
    MyStateMap(cpt.family, cpt.cs, newIds)
  }  

  /** Apply map to cpts. 
    * Pre: map is defined on all parameters of cpts. */
  private def applyRemapping(map: RemappingMap, cpts: Array[State])
      : Array[State] =
    cpts.map(cpt => applyRemappingToState(map, cpt))

  // ==================== Unification

  /** Try to extend map to map' st map'(st2) = st1.
    * If unsuccessful, map is unchanged.
    * @return true if successful. */
  private def unify(map: RemappingMap, st1: State, st2: State): Boolean = {
    // Work with map1, and update map only if successful. 
    val map1 = cloneMap(map) 
    if(st1.cs != st2.cs) false
    else{
      val ids1 = st1.ids; val ids2 = st2.ids
      val len = ids1.length; val typeMap = st1.typeMap
      assert(st1.family == st2.family && st2.typeMap == typeMap && 
        ids2.length == len)
      // Iterate through the parameters; ok indicates if matching successful
      // so far.
      var i = 0; var ok = true
      while(i < len && ok){
        val id1 = ids1(i); val id2 = ids2(i); val t = typeMap(i)
        if(isDistinguished(id1) || isDistinguished(id2)) ok = id1 == id2
        if(map1(t)(id2) < 0) map1(t)(id2) = id1 // extend map
        else ok = map1(t)(id2) == id1
        i += 1
      }
      if(ok) for(f <- 0 until numFamilies) map(f) = map1(f)
      ok
    }
  }

  /** Unifications between the components of two views, giving the indices of
    * components that are unified with one another. */
  type Unifications = List[(Int, Int)]

  /** Extend map, in all possible ways, to remap cpts2 so as to be compatible
    * with cpts1.  Each parameter (f,p), not in the domain of map, can be
    * mapped to an element of otherArgs(f) (a subset of the parameters of
    * cpts1), or a fresh value given by nextArg(f).  If an identity parameter
    * maps to an identity parameter of cpts1, then the corresponding States
    * much match.
    * 
    * @param map the RemappingMap that gets extended.  Cloned before being 
    * mutated.
    * @param nextArg a NextArgMap giving the next fresh parameter to use for 
    * each type.  Used mutably, but each update is backtracked.
    * @param otherArgs for each type, a list of other values that a parameter
    * can be mapped to.  Used mutably, but each update is backtracked.
    * @return all resulting maps. */
  private def combine1(map0: RemappingMap, nextArg: NextArgMap, 
    otherArgs: Array[List[Identity]], cpts1: Array[State], cpts2: Array[State]) 
      : ArrayBuffer[(RemappingMap, Unifications)] = {
    val result = new ArrayBuffer[(RemappingMap, Unifications)]

    // Extend map to remap cpts2(j).ids[i..) and then cpts2[j+1..). 
    def combineRec(map: RemappingMap, i: Int, j: Int, unifs: Unifications)
        : Unit = {
      // println(s"combineRec(${showRemappingMap(map)}, $i, $j)")
      if(j == cpts2.length) result += ((map, unifs))  // base case
      else{
        val c = cpts2(j); val ids = c.ids; val typeMap = c.typeMap
        if(i == ids.length) // End of this component
          combineRec(map, 0, j+1, unifs) // move on to the next component
        else{
          val id = ids(i); val f = typeMap(i)
          if(isDistinguished(id)) combineRec(map, i+1, j, unifs) // just move on
          else{ // rename (f, id)
            // Case 1: map id to the corresponding value in map, if any;
            // otherwise to an element id1 of otherArgs(f)
            val idX = map(f)(id) //; println(s"${(f,id)} -> $idX")
            val newIds = if(idX < 0) otherArgs(f) else List(idX)
            // println(s"idX = $idX; newIds = $newIds")
            for(id1 <- newIds){
              otherArgs(f) = newIds.filter(_ != id1) // temporary update (*)
              val map1 = extendMap(map, f, id, id1) // cloneMap(map); map1(f)(id) = id1 // IMPROVE
              if(i == 0){ // Identity; see if any cpt of cpts1 matches (f, id1)
                var matchedId = false // have we found a cpt with matching id?
                for(k <- 0 until cpts1.length){
                  val c1 = cpts1(k)
                  if(c1.componentProcessIdentity == (f,id1)){
                    assert(!matchedId); matchedId = true
                    println(s"  Trying to unify $c1 and $c")
                    if(c1.cs == c.cs && unify(map1, c, c)){
                      // println(showRemappingMap(map1))
                      combineRec(map1, 0, j+1, (k,j) :: unifs)
                    } 
                    else println("failed")
                  }
                } // end of for(k <- ...)
                if(!matchedId) // No cpt of cpts1 matched; move on
                  combineRec(map1, i+1, j, unifs)
              } // end of if(i == 0)
              else combineRec(map1, i+1, j, unifs) // Move on to next parameter
              otherArgs(f) = newIds // undo (*)
            } // end of for(id1 <- newIds)

            // Case 2: map id to nextArg(f)
            if(idX < 0){
              val id1 = nextArg(f); nextArg(f) += 1 // temporary update (+)
              val map1 = extendMap(map, f, id, id1) // cloneMap(map); map1(f)(id) = id1 // IMPROVE
              combineRec(map1, i+1, j, unifs) // Move on to next parameter
              nextArg(f) -= 1 // undo (+)
            }
          }
        }
      }
    } // end of combineRec

    combineRec(map0, 0, 0, List()); result
  }


  /** Try to combine two component views.  Produce all pi(v2), for remapping pi,
    * such that v1 U pi(v2) makes sense, i.e. the identities are disjoint. */
  def combine(v1: ComponentView, v2: ComponentView)
      : List[(Array[State], Unifications)] = {
    // println(s"combine($v1, $v2)")
    val servers = v1.servers; require(v2.servers == servers)
    val components1 = v1.components; val components2 = v2.components
    // The initial maps: map0 is the identity on the server parameters;
    // otherArgs gives parameters used in v1 but not the servers; nextArg
    // gives the next fresh parameters.
    val (map0, otherArgs, nextArg) = createMaps(servers, components1)
    // println(s"nextArg = "+nextArg.mkString(", "))
    // println(s"otherArgs = "+otherArgs.mkString(", "))

    val maps = combine1(map0, nextArg, otherArgs, components1, components2)
    // println(s"combine: "+maps.size+" results")
    // println(maps.map(showRemappingMap).mkString("\n"))
    maps.map{ 
      case (map, unifs) => (applyRemapping(map, components2), unifs) }.toList
  }

  /** All ways of remapping certain states of states, consistent with map0,
    * otherArgs and nextArg, so that its identity maps to id.  If selector =
    * Left(i) then just the non-identity parameters of states(i) are renamed.
    * If selector = Right(i) then every state except states(i) is renamed.
    * Each parameter (f,id) not in the domain of map0 can be mapped to an
    * element of otherArgs(f), or a fresh value given by nextArg(f). */
  private def remapXXX(
    map0: RemappingMap, otherArgs: OtherArgMap, nextArg: NextArgMap,
    states: Array[State], selector: Either[Int, Int]) 
      : ArrayBuffer[RemappingMap] = {
    val result = ArrayBuffer[RemappingMap]()

    /* Extend map to remap states(i).ids[j..), then states[i+1..).  Add each
     * resulting map to result.  map is treated immutably, but cloned.
     * otherArgs and nextArg are treated mutably, but all updates are
     * backtracked.*/
    def rec(map: RemappingMap, i: Int, j: Int): Unit = {
      if(i == states.length || selector == Left(i-1)) 
        result += map // base case
      else if(selector == Right(i)){  // skip this component
        assert(j == 0); rec(map, i+1, 0) 
      }
      else{
        // IMPROVE: turn following into variables in outer scope; set when j = 0.
        val st = states(i); val ids = st.ids; val typeMap = st.typeMap
        if(j == ids.length) rec(map, i+1, 0)
        else{
          val f = typeMap(j); val id = ids(j) // remap (f,id)
          if(isDistinguished(id) || map(f)(id) >= 0)
            rec(map, i, j+1) // just move on
          else{
            // Case 1: map id to an element id1 of otherArgs(f)
            val newIds = otherArgs(f)
            for(id1 <- newIds){
              otherArgs(f) = newIds.filter(_ != id1) // temporary update (*)
              rec(extendMap(map, f, id, id1), i, j+1)
            }
            otherArgs(f) = newIds                    // undo (*)

            // Case 2: map id to nextArg(f)
            val id1 = nextArg(f); nextArg(f) += 1   // temporary update (+)
            rec(extendMap(map, f, id, id1), i, j+1) // Move on to next parameter
            nextArg(f) -= 1                         // undo (+)
          }
        }
      }
    } // end of rec
   
    selector match{ 
      case Left(i) => rec(map0, i, 1)
      case Right(_) => rec(map0, 0, 0)
    }
    result
  }


  /** All ways of remapping cpts(i), consistent with map0, otherArgs and
    * nextArg, so that its identity maps to id.  Each parameter (f,id) not in
    * the domain of map0 can be mapped to an element of otherArgs(f), or a
    * fresh value given by nextArg(f). */
  def remapToId(map0: RemappingMap, otherArgs: OtherArgMap, nextArg: NextArgMap,
    cpts: Array[State], i: Int, id: Identity)
      : ArrayBuffer[RemappingMap] = {
    val st = cpts(i); val f = st.family; val id0 = st.ids(0); 
    // val len = ids.length
    assert(map0(f)(id0) < 0); map0(f)(id0) = id
    // val typeMap = st.typeMap
    // val result = ArrayBuffer[RemappingMap]()
    
    /* Extend map to remap ids[i..).  Add each resulting map to result. 
     * map is treated immutably, but cloned.  otherArgs and nextArg are treated
     * mutably, but all updates are backtracked.*/
    // def rec(map: RemappingMap, i: Int): Unit = {
    //   if(i == len) result += map 
    //   else{
    //     val f = typeMap(i); val id1 = ids(i) // remap (f,id1)
    //     if(isDistinguished(id1) || map(f)(id1) >= 0) 
    //       rec(map, i+1) // just move on
    //     else{
    //       // Case 1: map id1 to an element id2 of otherArgs(f)
    //       val newIds = otherArgs(f)
    //       for(id2 <- newIds){
    //         otherArgs(f) = newIds.filter(_ != id2) // temporary update (*)
    //         rec(extendMap(map, f, id1, id2), i+1)
    //       }
    //       otherArgs(f) = newIds                    // undo (*)

    //       // Case 2: map id1 to nextArg(f)
    //       val id2 = nextArg(f); nextArg(f) += 1 // temporary update (+)
    //       rec(extendMap(map, f, id1, id2), i+1) // Move on to next parameter
    //       nextArg(f) -= 1                       // undo (+)
    //     }
    //   }
    // } // end of rec

    //rec(map0, 1); 
    // println(result.map(showRemappingMap).mkString("; "))
    //result
    remapXXX(map0, otherArgs, nextArg, cpts, Left(i)) // IMPROVE
  }

  def remapRest(
    map0: RemappingMap, otherArgs: OtherArgMap, cpts: Array[State], i: Int)
      : ArrayBuffer[Array[State]] = {
    // IMPROVE: if cpts is a singleton, this can be simplified -- just map0
    val nextArg = new Array[Int](numTypes)
    for(f <- 0 until numFamilies; id <- map0(f))
      nextArg(f) = nextArg(f) max (id+1)
    val maps = remapXXX(map0, otherArgs, nextArg, cpts, Right(i))
    for(map <- maps) yield applyRemapping(map, cpts)
  }


  def combineTest = {
    ???
  }

}



///////////////////////////////////////////////////////
///////////////////////////////////////////////////////
// Dead code below



  // ----- Array[StateIndex]

  // private type StateIndexArray = Array[StateIndex]

  /** Maximum size of Array[StateIndex] pooled. */
  // private val MaxViewSize = 7 // Views.MaxViewSize FIXME

  // /** Maximum number of StateIndexArrays to store for each size.  
  //   * The two remapSplit*Canonical functions use two such.  */
  // private val MaxStateIndexPoolSize = 2

  /** Class for managing pool of StateIndexArrays; owned by a single thread. */
  // private class StateIndexPool{
  //   /** pools(i) stores a pool of StateIndexArrays of size i. */
  //   private val pools = Array.fill(MaxViewSize+1)(
  //     new Array[StateIndexArray](MaxStateIndexPoolSize))

  //   /** counts(i) stores the number of StateIndexArrays of size i stored. */
  //   private val counts = new Array[Int](MaxViewSize+1)

  //   /** Get a StateIndexArray of size size, maybe reusing a previous one. */
  //   @inline def get(size: Int): StateIndexArray = 
  //     if(counts(size) > 0){ counts(size) -= 1; pools(size)(counts(size)) } 
  //     else new StateIndexArray(size)

  //   /** Return a for recycling. */
  //   @inline def put(a: StateIndexArray) = {
  //     val size = a.length
  //     if(counts(size) < MaxStateIndexPoolSize){
  //       pools(size)(counts(size)) = a; counts(size) += 1
  //     }
  //     else Profiler.count("StateIndexPool.put fail"+size)
  //   }
  // } // End of StateIndexPool

  // /** Thread-local supply of StateIndexArrays. */
  // private object ThreadLocalStateIndexPool extends ThreadLocal[StateIndexPool]{
  //   override def initialValue() = { 
  //     // Profiler.count("TLSIP.init")
  //     new StateIndexPool
  //   }
  // }

  /** Get a StateIndexArray of size size, maybe reusing a previous one. */
  // @inline private def newStateIndexArray(size: Int): StateIndexArray = 
  //   ThreadLocalStateIndexPool.get.get(size)

  // /** Return a StateIndexArray for recycling. */
  // @inline def returnStateIndexArray(a: StateIndexArray) =
  //   ThreadLocalStateIndexPool.get.put(a)



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

  // val SplitFreshVal = State.SplitFreshVal

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




