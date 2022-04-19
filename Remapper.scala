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
    while(t < numTypes){ 
      map1(t) = map(t).clone; 
      // val size = map(t).size
      // map1(t) = new Array[Int](size); var i = 0
      // while(i < size){ map1(t)(i) = map(t)(i); i += 1 }
      t += 1 
    }
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

  /** Are map1 and map2 equivalent? */
  def equivalent(map1: RemappingMap, map2: RemappingMap): Boolean = {
    var t = 0; var same = true
    while(t < numTypes && same){
      // compare map1(t) and map2(t)
      var i = 0; val len = map1(t).size
      while(i < len && map1(t)(i) == map2(t)(i)) i += 1
      same = (i == len); t += 1
    }
    same
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

  /** A bitmap showing the range of map. */
  def rangeBitMap(map: RemappingMap): BitMap = {
    val bitmap = 
      Array.tabulate(numTypes)(t => new Array[Boolean](2*typeSizes(t)+2))
    // Note: the size above is a bit arbitrary.  FIXME
    for(t <- 0 until numTypes; i <- 0 until map(t).length){
      val id = map(t)(i); if(id >= 0) bitmap(t)(id) = true
    }
    bitmap
  }

  import ServersReducedMap.ReducedMap // = Array[Long]

  /** Convert map into a ReducedMap.  Each pair x -> y (y >= 0) of type t is
    * represented by summarise(t,x,y) (16 bits); these are in lexicographic
    * order of (t,x), concatenated into an Array[Long]. */
  def reduceMap(map: RemappingMap): ReducedMap = {
    // Calculate number of x values overall to consider
    var t = 0; var len = 0
    while(t < numTypes){ len += map(t).length; t += 1 }

    // We combine together the summary of four maplets into bits, and then put
    // them into results0.  At each point, we have included k maplets in bits,
    // and the remainder in results0[0..i)
    var bits = 0L; var k = 0
    val result0 = new Array[Long](((len-1) >> 2) + 1) // size = ceiling(len/4)
    t = 0; var i = 0 // result in result0[0..i)
    while(t < numTypes){
      var x = 0; val thisLen = map(t).length 
      //assert(thisLen < (1 << 7))
      while(x < thisLen){
        val y = map(t)(x)
        if(y >= 0){
          val summary = summarise(t,x,y); 
          //assert(0 < summary && summary < 65536)
          bits = (bits << 16) + summary; k += 1
          if(k == 4){ result0(i) = summary; i += 1; bits = 0; k = 0 }
        }
        x += 1
      }
      t += 1
    }

    //Profiler.count("rangeRestrictTo"+(4*i+k))
    // Normally 1 to 4, but sometimes more or less
    if(k > 0){ result0(i) = bits; i += 1 }
    // Copy into new array
    val result = new Array[Long](i); var j = 0
    while(j < i){ result(j) = result0(j); j += 1 }

    result
  }

  /** The range restriction of map to the parameters of servers, i.e. 
    * 
    * { x -> y | (x -> y) in map, y is a parameter of servers }.
    * 
    * The precise form of the result isn't important, other than equality
    * corresponding to equality of the above expression; but each pair x -> y
    * of type t is represented by summarise(t,x,y) (16 bits); these are in
    * lexicographic order of (t,x), concatenated into an Array[Long].  */
  def rangeRestrictTo(map: RemappingMap, servers: ServerStates)
      : ReducedMap = {
    val sIds = servers.idsBitMap

    // Calculate number of x values overall to consider
    var t = 0; var len = 0
    while(t < numTypes){ len += map(t).length; t += 1 }

    // We combine together the summary of four maplets into bits, and then put
    // them into results0.  At each point, we have included k maplets in bits,
    // and the remainder in results0[0..i)
    var bits = 0L; var k = 0
    val result0 = new Array[Long](((len-1) >> 2) + 1) // size = ceiling(len/4)
    t = 0; var i = 0 // result in result0[0..i)
    while(t < numTypes){
      val thisSIds = sIds(t); val sidsLen = thisSIds.length; 
      // var tResult = List[Int]()
      var x = 0; val thisLen = map(t).length 
      //assert(sidsLen < (1 << 7) && thisLen < (1 << 7))
      while(x < thisLen){
        val y = map(t)(x)
        if(y >= 0 && y < sidsLen && thisSIds(y)){
          val summary = summarise(t,x,y); 
          //assert(0 < summary && summary < 65536)
          bits = (bits << 16) + summary; k += 1
          if(k == 4){ result0(i) = summary; i += 1; bits = 0; k = 0 }
        }
        x += 1
      }
      t += 1
    }

    //Profiler.count("rangeRestrictTo"+(4*i+k))
    // Normally 1 to 4, but sometimes more or less
    if(k > 0){ result0(i) = bits; i += 1 }
    // Copy into new array
    val result = new Array[Long](i); var j = 0
    while(j < i){ result(j) = result0(j); j += 1 }

    result
  }  

  // The following assumption is necessary to ensure summarise forms a bijection.
  assert(numTypes > 0 && numTypes <= 4)

  /** Summarise t, x and y into 16 bits.  This assumes 0 <= t < 4, 0 <= x <
    * (1<<7), and 0 <= y < (1<<7).  This mapping forms an injection over such
    * values. */
  @inline private[RemapperP] 
  def summarise(t: Int, x: Int, y: Int) = (x << 9)+(t << 7) + y + 1
  // Note: the +1 ensures the result is non-zero

  /** The restriction of a RemappingMap, as used in crossRef, below. */
  type ResMap = Array[Int]

  /** The domain restriction of map to the parameters of c:
    * 
    *   { x -> y | (x -> y) \in map, x is a parameter of c}.
    * 
    * As with rangeRestrictTo, the representation isn't important, other than
    * value equality corresponding to the above expression.  However, we
    * consider the parameters of c in order, and record the values each maps
    * to. */
// IMPROVE representation
  def domainRestrictTo(map: RemappingMap, c: State): ResMap = {
    var result = new Array[Int](c.length); var i = 0
    while(i < c.length){
      val id = c.ids(i)
      if(isDistinguished(id)) result(i) = id
      else{ 
        val t = c.typeMap(i); 
        assert(id < map(t).length)
        result(i) = map(t)(id) 
      }
      i += 1
    }
    result
  }



  /** map domain restricted to the parameters of v.components, and range
    * restricted to the parameters of servers, i.e.
    * 
    * { x -> y | (x -> y) in map, x is a parameter of v.components and 
    *            y is a parameter of servers }.
    * 
    * The precise form of the result isn't important, other than equality
    * corresponding to equality of the above expression; but the types are in
    * reverse order; and the pairs for each type are in reverse order of x
    * components.
    * 
    * In fact, this gives no advantage over rangeRestrictTo. */
//   def restrictTo(map: RemappingMap, v: ComponentView, servers: ServerStates)
//       : ReducedMap = {
// // IMPROVE: use bit map for servers' parameters
//     val vParams = v.cptParamBitMap
//     var result = List[List[(Identity,Identity)]]()
//     for(t <- 0 until numTypes){
//       val sIds = servers.serverIds(t); var tResult = List[(Identity,Identity)]()
//       for(id <- 0 until map(t).length){
//         val y = map(t)(id); 
//         if(y >= 0 && vParams(t)(id) && sIds.contains(y)) tResult ::= (id, y)
//       }
//       result ::= tResult
//     }
//     result
//   }

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
    val serverNumParams = servers.paramsBound // numParams
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

  /** Normalise st, returning the normalised version and the remapping map to
    * produce it. */
  @inline def normaliseState(st: State): (State, RemappingMap) = {
    val map = newRemappingMap; val st1 = remapState(map, newNextArgMap, st)
    (st1, map)
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

  /** Remap components so they are in normal form based on servers.  Pre:
    * servers are normalised. */
  @inline def remapComponents(servers: ServerStates, components: Array[State])
      : Array[State] = 
    remapStates(servers.remappingMap, servers.nextArgMap, components)

  /** Make a ComponentView from servers, principal and others, remapping to
    * canonical form. */
  @inline def mkComponentView(
    servers: ServerStates, components: Array[State]) = {
    assert(components.forall(_ != null)) // IMPROVE
    val (servers1, map, nextArg) = remapServerStates(servers)
    val components1 = remapStates(map, nextArg, components)
    new ComponentView(servers1, components1) // principal1, others1)
  }

  def remapView(cv: ComponentView) = remapComponentView(cv)
  // IMPROVE

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
    // IMPROVE: could use a smaller remappingMap
    remapState(servers.remappingMap, servers.nextArgMap, st)
  }
}
