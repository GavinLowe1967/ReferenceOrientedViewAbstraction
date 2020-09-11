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
  private type RemappingMap = Array[Array[Identity]]

  def showRemappingMap(map: RemappingMap) = 
    map.map(_.mkString("[",",","]")).mkString("; ")

  /** A clear RemappingMap, representing the empty mapping; used as a
    * template for creating more such. */
  private val remappingMapTemplate: RemappingMap = 
    Array.tabulate(numTypes)(t => Array.fill(rowSizes(t))(-1))

  /** A thread-local RemappingMap. */
  // private object ThreadLocalRemappingMap extends ThreadLocal[RemappingMap]{
  //   override def initialValue() = {
  //     Array.tabulate(numTypes)(t => Array.fill(rowSizes(t))(-1))
  //   }
  // }

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
  private def applyRemappingToState(map: RemappingMap, cpt: State): State = {
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


// Check below.  In main function, rename identities to fresh parameters, then
// call this.

  /** Extend map, in all possible ways, to remap ids[i..) and then cpts, so that
    * each parameter other than the identities gets mapped (injectively)
    * either to a parameter of otherArgs or a fresh parameter (given by
    * nextArg).
    * @param map the RemappingMap that gets extended.  Used immutably.
    * @param nextArg a NextArgMap giving the next fresh parameter to use for 
    * each type.  Used mutably, but each update is backtracked.
    * @param otherArgs for each type, a list of other values that a parameter
    * can be mapped to.  Used mutably, but each update is backtracked.
    * @param typeMap a type map giving the types of ids.
    * @return all resulting maps. */
  // private def extendMapToCombineParams(map: RemappingMap, nextArg: NextArgMap, 
  //   otherArgs: Array[List[Identity]], ids: Array[Identity], i: Int,
  //   typeMap: Array[Type], cpts: List[State])
  //     : List[RemappingMap] = {
  //   if(i == ids.length){
  //     if(cpts.isEmpty) List(map) // base case
  //     else{ // move on to next component
  //       val c = cpts.head
  //       extendMapToCombineParams(
  //         map, nextArg, otherArgs, c.ids, 1, c.typeMap, cpts.tail)
  //     }
  //   } // end of if(i == ids.length)
  //   else{
  //     val id = ids(i); val f = typeMap(i) // rename (f,id)
  //     var result = List[RemappingMap]()

  //     // Case 1: map id to an element of otherArgs(f)
  //     val newIds = otherArgs(f)
  //     for(id1 <- newIds){
  //       otherArgs(f) = newIds.filter(_ != id1) // temporary update (*)
  //       val map1 = cloneMap(map); map1(f)(id) = id1 // IMPROVE
  //       val newMaps = extendMapToCombineParams(
  //         map1, nextArg, otherArgs, ids, i+1, typeMap, cpts)
  //       result = newMaps++result
  //     }
  //     otherArgs(f) = newIds // undo (*)

  //     // Case 2: map id to nextArg(f)
  //     val id1 = nextArg(f); nextArg(f) += 1 // temporary update (+)
  //     val map1 = cloneMap(map); map1(f)(id) = id1 // IMPROVE
  //     val newMaps = extendMapToCombineParams(
  //       map1, nextArg, otherArgs, ids, i+1, typeMap, cpts)
  //     result = newMaps++result
  //     nextArg(f) -= 1 // undo (+)

  //     result
  //   }
  // }

  /** Create a RemappingMap map that is the identity map on the identities of
    * servers, and that if a server references both a component c1 in
    * components1 and a component c2 in components2, then map(c2) = c1.  Or
    * return null if this is not possible. */
  // private def unifyCommonReferencedComponents(
  //   servers: ServerStates, components1: Array[State], components2: Array[State])
  //     :RemappingMap = {
  //   // The initial RenamingMap, the identity on the server parameters
  //   var map = createMap(servers.rhoS)

  //   // For each component c2 in v2, if its identity is referenced by a server
  //   // and matches the identity of a component of v1, then they must be
  //   // unifiable, or the combination fails.
  //   var i = 0; var ok = true
  //   while(i < components2.length && ok){
  //     val c2 = components2(i)
  //     val pId2 @ (f,id) = c2.componentProcessIdentity
  //     if(servers.serverIds(f).contains(id)){ // c2 is refed by a server
  //       // Find components of v1 with same process id.
  //       val matches = components1.filter(_.componentProcessIdentity == pId2)
  //       if(matches.nonEmpty){
  //         assert(matches.length == 1); val c1 = matches.head
  //         if(true || c1 != c2){
  //           print(s"Unifying $c1 and $c2... ")
  //           ok = unify(map, c1, c2)
  //           assert(!ok) // FIXME:
  //           // FIXME: if ok, I think remove this component from the list
  //         }
  //         else println(s"Not unifying $c1 with itself.")
  //       }
  //     } // end of if(servers.rhoS(t).contains(id))
  //     i += 1
  //   }

  //   if(ok) map else null
  // }


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
      : ArrayBuffer[RemappingMap] = {
    val result = new ArrayBuffer[RemappingMap]

    // Extend map to remap cpts2(j).ids[i..) and then cpts2[j+1..). 
    def combineRec(map: RemappingMap, i: Int, j: Int): Unit = {
      // println(s"combineRec(${showRemappingMap(map)}, $i, $j)")
      if(j == cpts2.length) result += map  // base case
      else{
        val c = cpts2(j); val ids = c.ids; val typeMap = c.typeMap
        if(i == ids.length) // End of this component
          combineRec(map, 0, j+1) // move on to the next component
        else{
          val id = ids(i); val f = typeMap(i)
          if(isDistinguished(id)) combineRec(map, i+1, j) // just move on
          else{ // rename (f, id)
            // Case 1: map id to an element id1 of otherArgs(f)
            val newIds = otherArgs(f)
            for(id1 <- newIds){
              otherArgs(f) = newIds.filter(_ != id1) // temporary update (*)
              val map1 = cloneMap(map); map1(f)(id) = id1 // IMPROVE
              if(i == 0){
                // Identity ; see if any component of cpts1 matches (f, id1)
                val matches = cpts1.filter(_.componentProcessIdentity == (f,id1))
                if(matches.nonEmpty){
                  assert(matches.length == 1); val c1 = matches.head
                  println(s"Trying to unify $c1 and $c")
                  if(unify(map1, c1, c)){
                    println(showRemappingMap(map1))
// FIXME: need to replace with corresp cpt in post-state
                    combineRec(map1, 0, j+1) // move on to next component
                  }
                  else{ println("failed"); combineRec(map1, i+1, j) }
                } // end of if(matches.nonEmpty)
                else // No component of cpts1 matched; move on to next parameter
                  combineRec(map1, i+1, j)
              } // end of if(i == 0)
              else combineRec(map1, i+1, j) // Move on to next parameter
              otherArgs(f) = newIds // undo (*)
            } // end of for(id1 <- newIds)

            // Case 2: map id to nextArg(f)
            val id1 = nextArg(f); nextArg(f) += 1 // temporary update (+)
            val map1 = cloneMap(map); map1(f)(id) = id1 // IMPROVE
            combineRec(map1, i+1, j) // Move on to next parameter
            nextArg(f) -= 1 // undo (+)
          }
        }
      }
    } // end of combineRec

    combineRec(map0, 0, 0); result
  }


  /** Try to combine two component views.  Produce all pi(v2), for remapping pi,
    * such that v1 U pi(v2) makes sense, i.e. the identities are disjoint. */
  def combine(v1: ComponentView, v2: ComponentView): List[Array[State]] = {
    // println(s"combine($v1, $v2)")
    val servers = v1.servers; require(v2.servers == servers)
    val components1 = v1.components; val components2 = v2.components

    // The initial map: the identity on the server parameters
    val rhoS = servers.rhoS; val map0 = createMap(rhoS)
    // The next fresh parameters
    val nextArg: NextArgMap = createNextArgMap(rhoS)
    // Parameters used in v1 but not the servers
    val otherArgs = Array.fill(numTypes)(List[Identity]())
    for(c <- v1.components; i <- 0 until c.ids.length){
      val f = c.typeMap(i); val id = c.ids(i)
      if(!rhoS(f).contains(id) && !otherArgs(f).contains(id)) 
        otherArgs(f) ::= id; nextArg(f) = nextArg(f) max (id+1)
    }
    // println(s"nextArg = "+nextArg.mkString(", "))
    // println(s"otherArgs = "+otherArgs.mkString(", "))

    val maps = combine1(map0, nextArg, otherArgs, components1, components2).toList

    // var map =  unifyCommonReferencedComponents(servers, components1, components2)

    // if(map != null){
    //   // The identities used in v1
    //   val cptIds1 = components1.map(_.componentProcessIdentity)
    //   // The next parameter of each type not used in v1
    //   // FIXME: wrong if some unification happened
    //   val nextArg: NextArgMap = createNextArgMap(servers.rhoS)
    //   // Parameters in v1 not as identities
    //   // FIXME: wrong if some unification happened
    //   val otherArgs = Array.tabulate(numTypes)(f =>
    //     servers.serverIds(f).filter(id => !cptIds1.contains((f,id))) )
    //   for(c <- v1.components; i <- 0 until c.ids.length){
    //     val f = c.typeMap(i); val id = c.ids(i)
    //     nextArg(f) = nextArg(f) max (id+1)
    //     if(i > 0) if(!otherArgs(f).contains(id)) otherArgs(f) ::= id
    //   }
    //   // println("map = "+map.map(_.mkString("[",",","]")).mkString("; "))
    //   // println("nextArg = "+nextArg.mkString("[",",","]")+
    //   //   "; otherArgs = "+otherArgs.mkString("; "))

    //   // Map each identity in v2 to a fresh parameter (given by nextArg)
    //   for(c <- components2){
    //     val ids = c.ids; val (f,id) = c.componentProcessIdentity
    //     assert(map(f)(id) < 0, s"c = $c; "+map(f)(id))
    //     // Map id to newId
    //     val newId = nextArg(f); nextArg(f) += 1; map(f)(id) = newId
    //   }

      // Now map each other parameter either to a fresh parameter or a
      // parameter of otherArgs
      // val c = components2.head
      // val maps = extendMapToCombineParams(
      //   map, nextArg, otherArgs, c.ids, 1, c.typeMap, components2.toList.tail)
      // for(map <- maps){
      //   // println(showRemappingMap(map))
      //   val newCpts = applyRemapping(map, components2)
      //   println(newCpts.mkString("[", ",", "]"))
      // }
    println(s"combine: "+maps.size+" results")
    println(maps.map(showRemappingMap).mkString("\n"))
    maps.map(map => applyRemapping(map, components2))
      // maps
    // }
    // else List()

  }

  def combineTest = {
    ???
  }

  /** Try to combine two lists of component states, consistent with map.
    * @return all extensions map' of map such that cpts1 U map'(cpts2) makes 
    * sense, i.e. the identities are disjoint. */
  // private def combineZZZ(map: RemappingMap, nextArg: NextArgMap, 
  //   otherArgs: Array[List[Identity]], cpts2: List[State])
  //     : List[RemappingMap] = {
  //   if(cpts2.isEmpty) List(map)
  //   else{
  //     val c1 = cpts2.head
  //     //val newMaps = extendMapToCombineState(map, nextArg, otherArgs, c1)
  //     // newMaps.flatMat(map1 => combineZZZ(map1, nextArg
  //     ???
  //   }
  // }

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


