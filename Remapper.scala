package ViewAbstraction.RemapperP 

import ViewAbstraction._
import ox.gavin.profiling.Profiler
import scala.math.Ordering.Implicits._ // for sorting list of lists
import scala.collection.mutable.{ArrayBuffer,HashMap}

/** Utility object to apply remapping of parameters in states.  
  * 
  * Some remapping functions take a ParamMap, showing which parameters should
  * be left unchanged.  Each function remaps parameters so that they, and
  * those in the ParamMap if applicable, form an initial segment of the
  * naturals, and their first occurences are in order. */ 
object Remapper{
  // ----- RemappingMaps


  /* The type of maps recording the values that parameters get remapped to.  
   * map(t)(arg) records the value that arg of type t gets remapped to,
   * or -1 if no value has been allocated yet.  I.e., it represents the
   * mapping
   *  {(t,arg) -> (t, map(t)(arg)) |
   *       0 <= t < numTypes, 0 <= arg < size(t), map(t)(arg) != -1}.
   */
  // type RemappingMap = Array[Array[Identity]]

  /** Show a remapping map. */
  def show(map: RemappingMap) = map.map(_.mkString("[",",","]")).mkString("; ") 

  /** Template from which to create RemappingMap. */
  private val remappingMapTemplate =
// FIXME: the "*2" below is arbitrary, and probably insufficient in some cases.
// Maybe chose the map's size on a case-by-case basis.
    Array.tabulate(numTypes)(t => Array.fill(2*typeSizes(t)+2)(-1))

  /** Produce a (deep) clone of map. */
  @inline def cloneMap(map: RemappingMap): RemappingMap = {
    val map1 = new Array[Array[Int]](numTypes); var t = 0
    while(t < numTypes){ map1(t) = map(t).clone; t += 1 }
    map1
  }

  /** A clear RemappingMap, representing the empty mapping, i.e. mapping all
    * entries to -1.  Different calls to this will use the same arrays, so two
    * RemappingMaps created by the same thread should not be in use at the
    * same time. */
  @inline def newRemappingMap: RemappingMap = cloneMap(remappingMapTemplate)

  /** Is the mapping represented by map injective? */
  def isInjective(map: RemappingMap): Boolean = {
    var ok = true; var f = 0
    while(ok && f < numTypes){
      var i = 0; val len = map(f).length
      while(ok && i < len-1){
        if(!isDistinguished(map(f)(i))){
          // check map(f)(i) not in map(f)[i+1..len)
          var j = i+1
          while(j < len && map(f)(j) != map(f)(i)) j += 1
          ok = j == len
        }
        i += 1
      }
      f += 1
    }
    ok
    }

  /** Produce a new RemappingMap, extending map0 so (f,id) maps to id1.
    * Note: the resulting map shares some entries with map0, so neither should 
    * be mutated.  Pre: this does not make the map non-injective. */
  def extendMap(
    map0: RemappingMap, f: Family, id: Identity, id1: Identity)
      : RemappingMap = {
    // id1 should not appear in map0(f), except perhaps in position id
    if(false){ // This is quite costly
      var i = 0
      while(i < map0(f).length){
        if(i != id)
          require(map0(f)(i) != id1,
            s"extendMap: value $id1 already appears in map: "+
              map0(f).mkString("[",",","]")+"; "+(id,id1))
        i += 1
      }
    }
    val result = new Array[Array[Int]](numTypes)
    var t = 0
    while(t < numTypes){
      if(t != f) result(t) = map0(t)
      else{ result(t) = map0(f).clone; result(t)(id) = id1 }
      t += 1
    }
    result
  }

  type RemappingList =  List[List[(Identity,Identity)]]

  /** The range restriction of map to the parameters of servers, i.e. 
    * 
    * { x -> y | (x -> y) in map, y is a parameter of servers }.
    * 
    * The precise form of the result isn't important, other than equality
    * corresponding to equality of the above expression; but the types are in
    * reverse order; and the pairs for each type are in reverse order of x
    * components. */
  def rangeRestrictTo(map: RemappingMap, servers: ServerStates)
      : RemappingList = {
    var result = List[List[(Identity,Identity)]]()
    for(t <- 0 until numTypes){
      val sIds = servers.serverIds(t); var tResult = List[(Identity,Identity)]()
      for(id <- 0 until map(t).length){
        val y = map(t)(id); if(sIds.contains(y)) tResult ::= (id, y)
      }
      result ::= tResult
    }
    result
  }

  // ------ NextArgMaps

  /** The type of maps giving the next argument to map a parameter of
    * type t.  The corresponding RemappingMap has domain all
    * parameters (t,i) for i <- [0..nextArg(t)), for each t. */
  // type NextArgMap = Array[Int]

  def show(nexts: NextArgMap) = nexts.mkString("[", ", ", "]")

  /** Create a new NextArgMap, corresponding to the empty mapping.  Equivalent
    * to new Array[Int](numTypes) */
  @inline private def newNextArgMap: NextArgMap = new Array[Int](numTypes)

  /* A list, for each type, of non-fresh values that a particular parameter can
   * be mapped to. */
  // type OtherArgMap = Array[List[Identity]]

  def newOtherArgMap: OtherArgMap = Array.fill(numTypes)(List[Identity]())

  def show(otherArgs: OtherArgMap) = otherArgs.mkString("[", ";", "]")

  /** Remove ran map from bitMap. */
  def removeFromBitMap(map: RemappingMap, bitMap: Array[Array[Boolean]]) = {
    var f = 0
    while(f < numFamilies){
      var i = 0; val len = map(f).length
      while(i < len){
        val id = map(f)(i); i += 1; if(id >= 0) bitMap(f)(id) = false
      }
      f += 1
    }
  }

  /** Create an OtherArgMap from a bitmap. */
  def makeOtherArgMap(bitMap: Array[Array[Boolean]]): OtherArgMap = {
    val otherArgs = newOtherArgMap; var f = 0
    while(f < numFamilies){
      var i = 0; val len = bitMap(f).size
      while(i < len){ if(bitMap(f)(i)) otherArgs(f) ::= i; i += 1 }
      f += 1
    }
    otherArgs
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
    *  Note: now inlined in Concretization.getCombiningMaps; only used in
    *  RemapperTest.
    */
  private [RemapperP]
  def createCombiningMaps(servers: ServerStates, components: Array[State])
      : (RemappingMap, OtherArgMap, NextArgMap) = {
    Profiler.count("createCombiningMaps")
    val map0 = servers.remappingMap // identity map on server ids
    val nextArg: NextArgMap = servers.nextArgMap  // The next fresh parameters
    // Parameters used in components but not the servers
    val otherArgs = Array.fill(numTypes)(List[Identity]()); var cix = 0
    // Iterate through params of components
    while(cix < components.length){
      val c = components(cix); val ids = c.ids; var i = 0
      while(i < ids.length){
        val f = c.typeMap(i); val id = ids(i); assert(id <= nextArg(f))
        if(id == nextArg(f)){ otherArgs(f) ::= id; nextArg(f) += 1 }
        i += 1
      }
      cix += 1
    }
    (map0, otherArgs, nextArg)
  }

  /** Create (1) an OtherArgMap giving the identities in components but not
    * servers; (2) a NextArgMap giving the next fresh parameters.  Called by
    * System.consistentStates. 
    * 
    * Example:
    * [21[-1](T0) || 22[-1](Null) || 23[-1]()] || [12[1](T0,N0) || 7[0](N0,N1)]
    * gives [List(1, 0);List()] (or permutations) and [2,1] */ 
  def createMaps1(servers: ServerStates, components: Array[State]) 
      : (OtherArgMap, NextArgMap) = {
    val otherArgs = Array.fill(numTypes)(List[Identity]())
    val serverNumParams = servers.numParams
    val nextArg = serverNumParams.clone // Note: need to clone
    for(st <- components; i <- 0 until st.ids.length){
      val f = st.typeMap(i); val id = st.ids(i)
      if(!isDistinguished(id) && id >= serverNumParams(f) && 
        !otherArgs(f).contains(id))
        otherArgs(f) ::= id; nextArg(f) = nextArg(f) max (id+1)
    }
    (otherArgs, nextArg)
  }

  /** New OtherArgMap, equivalent to otherArgs except with the parameters of st
    * removed. */
  def removeParamsOf(otherArgs: OtherArgMap, st: State): OtherArgMap = {
    val newOtherArgs = otherArgs.clone
    val typeMap = st.typeMap; val ids = st.ids
    for(j <- 0 until ids.length){
      val f1 = typeMap(j)
      newOtherArgs(f1) = newOtherArgs(f1).filter(_ != ids(j))
    }
    newOtherArgs
  }

  // /** An OtherArgMap, contaiing all the parameters in states that are not mapped
  //   * by map. */
  // def otherArgsFromStates(map: RemappingMap, states: Array[State])
  //     : OtherArgMap = {
  //   val otherArgs = newOtherArgMap; var i = 0
  //   while(i < states.length){
  //     val st = states(i); val ids = st.ids; val typeMap = st.typeMap; var j = 0
  //     while(j < ids.length){
  //       val f = typeMap(j); val id = ids(j)
  //       if(!isDistinguished(id) && map(f)(id) < 0){

  //   }
  // }

  // ======================================================= Helper functions

  /** Remap the parameter (t,arg), either following map, or by the next value
    * specified by arg; update map and arg appropriately. */
  @inline private def remapArg(
    map: RemappingMap, nextArg: NextArgMap, t: Type, arg: Identity)
      : Identity = {
    if(isDistinguished(arg)) arg
    else{
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
    assert(st != null) // IMPROVE
    val cs = st.cs; val ids = st.ids; val len = ids.length; var index = 0
    val remappedParams = new Array[Identity](len) // State.getIdentityArray(len) 
    val tArray = State.stateTypeMap(cs) // array giving types of ids
    while(index < len){
      remappedParams(index) = remapArg(map, nextArg, tArray(index), ids(index))
      index += 1
    }
    remappedParams
  }

  /** Remap a single state st, updating map and nextArg. */
  @inline 
  def remapState(map: RemappingMap, nextArg: NextArgMap, st: State): State = {
    val remappedParams = remapParams(map, nextArg, st)
    MyStateMap(st.family, st.cs, remappedParams)
  }

  /** Remap state st, returning its index; also update map and nextArg. */
  @inline private 
  def remapStateToIndex(map: RemappingMap, nextArg: NextArgMap, st: State)
      : StateIndex = {
    val remappedParams = remapParams(map, nextArg, st)
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

  // @inline private 
  // def remapServerStates(map: RemappingMap, nextArg: NextArgMap, ss: ServerStates)
  //     : ServerStates = 
  //   ServerStates(remapStates(map, nextArg, ss.servers))

  /** Cache used in remapServerStates. */
  private val remapSSCache = 
    new HashMap[ServerStates, (ServerStates, RemappingMap, NextArgMap)]

  /** Remap ss to normal form.  Also return resulting RemappingMap and
    * NextArgMap. */
  @inline private def remapServerStates(ss: ServerStates)
      : (ServerStates, RemappingMap, NextArgMap) = {
    remapSSCache.get(ss) match{ // Try to retrieve from cache. 
      case Some((ss1, map, nextArgs)) => 
        // Profiler.count("remapServerStates found")
        (ss1, cloneMap(map), nextArgs.clone)
      case None =>
        // Profiler.count("remapServerStates new")
        val map = newRemappingMap; var nextArg = newNextArgMap
        val servers = ServerStates(remapStates(map, nextArg, ss.servers))
        remapSSCache += ss -> ((servers, cloneMap(map), nextArg.clone))
        (servers, map, nextArg)
    }
  }

  // =================== Remapping views

  /** Remap a ComponentView. */
  @inline def remapComponentView(v: ComponentView): ComponentView = {
    val (servers1, map, nextArg) = remapServerStates(v.servers)
    val components1 = remapStates(map, nextArg, v.components)
    new ComponentView(servers1, components1) // principal1, others1)
  }

  /** Make a ComponentView from servers, principal and others, remapping to
    * canonical form. */
  @inline def mkComponentView(
    servers: ServerStates, components: Array[State]) = {
    assert(components.forall(_ != null)) // IMPROVE
    val (servers1, map, nextArg) = remapServerStates(servers)
    val components1 = remapStates(map, nextArg, components)
    new ComponentView(servers1, components1) // principal1, others1)
  }

  def remapView(v: View) = v match{
    case cv: ComponentView => remapComponentView(cv)
  }

  /** Apply map to cpt. 
    * Pre: map is defined on all parameters of cpt. */
  def applyRemappingToState(map: RemappingMap, cpt: State): State = {
    val typeMap = cpt.typeMap; val ids = cpt.ids; val len = ids.length
    val newIds = new Array[Identity](len); var i = 0
    while(i < len){
      val id = ids(i)
      if(isDistinguished(id)) newIds(i) = id 
      else{ 
        newIds(i) = map(typeMap(i))(id)
        assert(newIds(i) >= 0, 
          "applyMappingToState: map"+show(map)+" undefined at "+(i, id)+
            " for "+cpt)
      }
      i += 1
    }
    MyStateMap(cpt.family, cpt.cs, newIds)
  }  

  /** Apply map to cpts. 
    * Pre: map is defined on all parameters of cpts. */
  def applyRemapping(map: RemappingMap, cpts: Array[State]): Array[State] = {
    val len = cpts.length; val result = new Array[State](len); var i = 0
    while(i < len){
      result(i) = applyRemappingToState(map, cpts(i)); i += 1
    }
    result
  }

  /** Remap st so that it can be the principal component in a view with
    * servers. */
  def remapToPrincipal(servers: ServerStates, st: State): State = {
    remapState(servers.remappingMap, servers.nextArgMap, st)
  }


  // ==================== Unification

  /** Try to extend map to map' such that map'(st2) = st1.
    * Note: map is unchanged.
    * @return the new map, or null if unsuccessful. */
  // def unify(map: RemappingMap, st1: State, st2: State): RemappingMap = {
  //   // println(s"unify(${showRemappingMap(map)}, $st1, $st2)")
  //   if(st1.cs != st2.cs) null // false
  //   else{
  //     val map1 = cloneMap(map)
  //     val ids1 = st1.ids; val ids2 = st2.ids
  //     val len = ids1.length; val typeMap = st1.typeMap
  //     assert(st1.family == st2.family && st2.typeMap == typeMap && 
  //       ids2.length == len)
  //     // Iterate through the parameters; ok indicates if matching successful
  //     // so far.
  //     var i = 0; var ok = true
  //     while(i < len && ok){
  //       val id1 = ids1(i); val id2 = ids2(i); val t = typeMap(i)
  //       if(isDistinguished(id1) || isDistinguished(id2)) ok = id1 == id2
  //       else if(map1(t)(id2) < 0){
  //         if(map1(t).contains(id1)) ok = false // must preserve injectivity 
  //         else map1(t)(id2) = id1 // extend map
  //       }
  //       else ok = map1(t)(id2) == id1
  //       i += 1
  //     }
  //     if(ok) map1 else null 
  //   }
  // } 

  /** Unifications between the components of two views, giving the indices of
    * components that are unified with one another. */
  // type Unifications = List[(Int, Int)]

  // @volatile var renameXCount = 0L
  // @volatile var combineRecCount = 0L
  // @volatile var combine1Count = 0L
  //@volatile var combineCount = 0L

  /** Extend map, in all possible ways, to remap cpts2 so as to be compatible
    * with cpts1.  Each parameter (f,p), not in the domain of map, can be
    * mapped to an element of otherArgs(f) (a subset of the parameters of
    * cpts1), or a fresh value given by nextArg(f).  If the jth identity
    * parameter of cpts2 maps to the kth identity parameter of cpts1, then the
    * corresponding States much match, and the pair (k,j) is included in the
    * Unifications returned.  Called by combine.  See
    * RemapperTest.combine1Test for examples.
    * 
    * @param map the RemappingMap that gets extended.  Cloned before being 
    * mutated.
    * @param nextArg a NextArgMap giving the next fresh parameter to use for 
    * each type.  For each type, at least one more than the maximum of the
    * corresponding parameters of cpts1 and elements of map0 and otherArgs.
    * Used mutably, but each update is backtracked.
    * @param otherArgs for each type, a list of other values that a parameter
    * can be mapped to.  For each type, disjoint from the range of the
    * corresponding element of map0.  Used mutably, but each update is
    * backtracked.
    * @return all resulting remappings of cpts2 together with the 
    * unifications. */
  //private[RemapperP] 
  // def combine1(map0: RemappingMap, nextArg: NextArgMap,
  //   otherArgs: Array[List[Identity]], cpts1: Array[State], cpts2: Array[State]) 
  //     : ArrayBuffer[(Array[State], Unifications)] = {
  //   combine1Count += 1
  //   // Profiler.count("combine1")
  //   var f = 0
  //   // IMPROVE: following checks are expensive
  //   while(f < numTypes){
  //     // Check otherArgs(f) disjoint from ran(map0(f))
  //     var oa = otherArgs(f)
  //     while(oa.nonEmpty){
  //       require(!map0(f).contains(oa.head),
  //         s"combine1: otherArgs not disjoint from map0 for $f: "+
  //           map0(f).mkString("[",",","]")+"; "+otherArgs(f).mkString("[",",","]"))
  //       oa = oa.tail
  //     }
  //     // Check nextArg(f) holds next fresh value
  //     require(nextArg(f) > (
  //       if(otherArgs(f).isEmpty) map0(f).max 
  //       else(map0(f).max max otherArgs(f).max)  ),
  //       s"combine1: nextArg($f) with incorrect value: "+nextArg(f)+"; "+
  //         map0(f).mkString("[",",","]")+"; "+otherArgs(f).mkString("[",",","]"))
  //     f += 1
  //   }
  //   // Check elements of cpts1 are distinct
  //   // for(i <- 0 until cpts1.length; j <- i+1 until cpts1.length)
  //   //   assert(cpts1(i) != cpts1(j), View.showStates(cpts1))
  //   // println("combine1: "+showRemappingMap(map0)+"; "+
  //   //   nextArg.mkString("[",",","]")+"; "+otherArgs.mkString("[",",","]")+"; "+
  //   //   cpts1.mkString("[",",","]")+"; "+cpts2.mkString("[",",","]"))
  //   val result = new ArrayBuffer[(Array[State], Unifications)]

  //   // Extend map to remap cpts2(j).ids[i..) and then cpts2[j+1..). 
  //   def combineRec(map: RemappingMap, i: Int, j: Int, unifs: Unifications)
  //       : Unit = {
  //     combineRecCount += 1
  //     // Profiler.count("combineRec")
  //     // for(f <- 0 until numTypes) // IMPROVE
  //     //   require(otherArgs(f).forall(id => !map(f).contains(id)),
  //     //     s"combineRec: otherArgs not disjoint from map for $f: "+
  //     //  map(f).mkString("[",",","]")+"; "+otherArgs(f).mkString("[",",","]"))
  //     //require(isInjective(map), "combineRec: "+showRemappingMap(map))//IMPROVE
  //     // println(s"combineRec(${showRemappingMap(map)}, $i, $j)")
  //     if(j == cpts2.length) 
  //       result += ((applyRemapping(map, cpts2), unifs))  // base case
  //     else{
  //       val c = cpts2(j); val ids = c.ids; val typeMap = c.typeMap
  //       if(i == ids.length) // End of this component
  //         combineRec(map, 0, j+1, unifs) // move on to the next component
  //       else{
  //         val id = ids(i); val f = typeMap(i)
  //         if(isDistinguished(id)) combineRec(map, i+1, j, unifs) // just move on
  //         else{ // rename (f, id)
  //           // Case 1: map id to the corresponding value idX in map, if any;
  //           // otherwise to an element id1 of otherArgs(f).
  //           val idX = map(f)(id) 
  //           // Rename id to id1
  //           def renameX(id1: Identity) = {
  //             // Profiler.count("renameX"); 
  //             renameXCount += 1
  //             if(i == 0){ // Identity; see if any cpt of cpts1 matches (f, id1)
  //               var matchedId = false // have we found a cpt with matching id?
  //               var k = 0
  //               while(k < cpts1.length){
  //                 val c1 = cpts1(k)
  //                 if(c1.componentProcessIdentity == (f,id1)){
  //                   // val map1 = extendMap(map, f, id, id1)
  //                   assert(!matchedId, View.showStates(cpts1)+": "+(f,id1))
  //                   matchedId = true
  //                   // val map1 = extendMap(map, f, id, id1)
  //                   map(f)(id) = id1 // temporary update (*)
  //                   val map2 = unify(map, c1, c)
  //                   if(map2 != null){
  //                     // Update otherArgs to be disjoint from ran map2.
  //                     val oldOtherArgs = otherArgs.clone; var f1 = 0
  //                     while(f1 < numTypes){
  //                       // @noinline def XX = {
  //                       otherArgs(f1) = 
  //                         otherArgs(f1).filter(id => !map2(f1).contains(id)) // }
  //                       // XX
  //                       f1 += 1
  //                     }
  //                     combineRec(map2, 0, j+1, (k,j)::unifs)
  //                     // Undo previous update
  //                     f1 = 0
  //                     while(f1 < numTypes){
  //                       otherArgs(f1) = oldOtherArgs(f1); f1 += 1
  //                     }
  //                   }
  //                   map(f)(id) = idX // backtrack (*)
  //                 }
  //                 k += 1
  //               } // end of while(k < ...)
  //               if(!matchedId){ // No cpt of cpts1 matched; move on   
  //                 map(f)(id) = id1 // temporary update (*)
  //                 combineRec(map, i+1, j, unifs) 
  //                 map(f)(id) = idX // backtrack (*)
  //               }
  //             } // end of if(i == 0)
  //             else{  // Move on to next parameter
  //               map(f)(id) = id1  // temporary update (*)
  //               combineRec(map, i+1, j, unifs)
  //               map(f)(id) = idX // backtrack (*)
  //             }
  //           } // end of renameX

  //           if(idX < 0){
  //             // Call renameX for each id1 in otherArgs(f), with id1 removed
  //             // from otherArgs(f).  toDoIds represents the identities still
  //             // to deal with; doneIds is those already done.
  //             var toDoIds = otherArgs(f); var doneIds = List[Identity]()
  //             // Profiler.count("combineRec"+toDoIds.length)
  //             // 0: 5%; 1: 60%; 2: 30%; 3: 5%
  //             while(toDoIds.nonEmpty){
  //               val id1 = toDoIds.head; toDoIds = toDoIds.tail
  //               otherArgs(f) = doneIds++toDoIds // temporary update (*)
  //               renameX(id1)
  //               doneIds = id1::doneIds // doneIds:+id1 -- order doesn't matter
  //             }
  //             otherArgs(f) = doneIds // undo (*)
  //           }
  //           else{ 
  //             // assert(!otherArgs(f).contains(idX), 
  //             //   show(map)+"; "+f+"; "+otherArgs(f))
  //             renameX(idX) 
  //           }

  //           // Case 2: map id to nextArg(f)
  //           if(idX < 0){ 
  //             val id1 = nextArg(f); nextArg(f) += 1 // temporary update (+)
  //             map(f)(id) = id1 // (+)  // val map1 = extendMap(map, f, id, id1) 
  //             combineRec(map, i+1, j, unifs) // Move on to next parameter
  //             nextArg(f) -= 1; map(f)(id) = idX  // undo (+)
  //           }
  //         }
  //       }
  //     }
  //   } // end of combineRec

  //   combineRec(map0, 0, 0, List()); result
  // }

  /** Try to combine two component views.  Produce all pi(v2), for remapping pi,
    * such that v1 U pi(v2) makes sense, i.e. agree on common components.  If
    * the jth identity parameter of v2 maps to the kth identity parameter of
    * v1, then the corresponding States much match, and the pair (k,j) is
    * included in the Unifications returned. */
  // def combine(v1: Concretization, v2: ComponentView)
  //     : ArrayBuffer[(Array[State], Unifications)] = {
  //   //combineCount += 1
  //   // println(s"combine($v1, $v2)")
  //   val servers = v1.servers; require(v2.servers == servers)
  //   val components1 = v1.components; val components2 = v2.components
  //   View.checkDistinct(components2)
  //   // The initial maps: map0 is the identity on the server parameters;
  //   // otherArgs gives parameters used in v1 but not the servers; nextArg
  //   // gives the next fresh parameters.
  //   val (map0, otherArgs, nextArg) = createCombiningMaps(servers, components1)
  //   // IMPROVE: inline combine1
  //   combine1(map0, nextArg, otherArgs, components1, components2)
  // }

}
