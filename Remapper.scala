package ViewAbstraction.RemapperP 

import ViewAbstraction._
import ViewAbstraction.collection.ShardedHashMap
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

  /** Produce a (deep) clone of map. */
  @inline def cloneMap(map: RemappingMap): RemappingMap = {
    Pools.cloneMap(map)
    // val map1 = Pools.getRemappingMap; var t = 0 
    // while(t < numTypes){ map1(t) = Pools.cloneRow(map(t)); t += 1 }
    // map1
  }

  /** The size for the remapping map for type t.  */
// FIXME: the "*2" below is arbitrary, and probably insufficient in some cases. 
  @inline private def sizeForRemapping(t: Type) = 2*typeSizes(t)+2

  /** Template from which to create RemappingMap. */
  private val remappingMapTemplate =
// Maybe chose the map's size on a case-by-case basis.
    Array.tabulate(numTypes)(t => Array.fill(sizeForRemapping(t))(-1))

  /** A clear RemappingMap, representing the empty mapping, i.e. mapping all
    * entries to -1.  Different calls to this will use the same arrays, so two
    * RemappingMaps created by the same thread should not be in use at the
    * same time. */
  @inline def newRemappingMap: RemappingMap = {
    // Profiler.count("newRemappingMap")
    val map1 = Pools.getRemappingMap; var t = 0
    while(t < numTypes){ map1(t) = remappingMapTemplate(t).clone; t += 1 }
    map1
  }

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

  /** Produce a new RemappingMap, extending map0 so (f,id) maps to id1.  Pre:
    * this does not make the map non-injective. */
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
    val result = Pools.getRemappingMap; var t = 0
    while(t < numTypes){
      result(t) = Pools.cloneRow(map0(t))
      if(t == f) result(t)(id) = id1
      // Note: previous version allowed the resulting map to share some
      // entries with map0, so neither could be mutated or recycled.
      // if(t != f) result(t) = map0(t)
      // else{ 
      //   result(t) = Pools.cloneRow(map0(f)) //map0(f).clone;
      //   result(t)(id) = id1
      // }
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

  /** A total inverse of a total map.  */
  def inverse(map: RemappingMap): RemappingMap = {
    require(isInjective(map))
    // If x -> y in map, then we include y -> x in the result. 
    val result = Array.tabulate(numTypes)(t => new Array[Int](map(t).length))
    for(t <- 0 until numTypes){
      // For each x -> y of type t in map, add y -> x
      for(x <- 0 until map(t).size){
        val y = map(t)(x); require(y >= 0); result(t)(y) = x
      }
    }
    assert(isInjective(result), show(map)+"\n"+show(result))
    result
  }

  /** An array holding the Parameters renamed to a new value, and an array
    * holding what they get remapped to (in the same order). */
  def getFromsTos(map: RemappingMap): (Array[Parameter], Array[Parameter]) = {
    var froms = List[Parameter](); var tos = List[Parameter]()
    for(t <- 0 until numTypes; id <- 0 until map(t).length){
      val id1 = map(t)(id)
      if(id1 >= 0 && id1 != id){ froms ::= ((t, id)); tos ::= ((t, id1)) }
    }
    (froms.toArray, tos.toArray)
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
          if(k == 4){ result0(i) = bits; i += 1; bits = 0; k = 0 }
        }
        x += 1
      }
      t += 1
    }

    //Profiler.count("rangeRestrictTo"+(4*i+k))
    // Normally 1 to 4, but sometimes more or less
    if(k > 0){ result0(i) = bits; i += 1 }
    // Copy into new array
    truncate(result0, i)
    // val result = new Array[Long](i); var j = 0
    // while(j < i){ result(j) = result0(j); j += 1 }
    // result
  }

  /** Truncate result0 to length entries. */
  @inline private def truncate(result0: Array[Long], length: Int)
      : Array[Long] = {
    Profiler.count("truncate: "+(result0.length == length))
    if(result0.length == length) result0 
    else{
      val result = new Array[Long](length); var j = 0
      while(j < length){ result(j) = result0(j); j += 1 }
      result
    }
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
      val thisSIds = sIds(t); val sidsLen = thisSIds.length
      var x = 0; val thisLen = map(t).length 
      //assert(sidsLen < (1 << 7) && thisLen < (1 << 7))
      while(x < thisLen){
        val y = map(t)(x)
        if(y >= 0 && y < sidsLen && thisSIds(y)){
          val summary = summarise(t,x,y); 
          //assert(0 < summary && summary < 65536)
          bits = (bits << 16) + summary; k += 1
          if(k == 4){ result0(i) = bits; i += 1; bits = 0; k = 0 }
        }
        x += 1
      }
      t += 1
    }

    //Profiler.count("rangeRestrictTo"+(4*i+k))
    // Normally 1 to 4, but sometimes more or less
    if(k > 0){ result0(i) = bits; i += 1 }
    // Copy into new array
    truncate(result0, i)
    // val result = new Array[Long](i); var j = 0
    // while(j < i){ result(j) = result0(j); j += 1 }
    // result
  }  

  // The following assumption is necessary to ensure summarise forms a bijection.
  assert(numTypes > 0 && numTypes <= 4)

  /** Summarise t, x and y into 16 bits.  This assumes 0 <= t < 4, 0 <= x <
    * (1<<7), and 0 <= y < (1<<7)-1.  This mapping forms an injection over such
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

  /** Extend map, mapping all undefined values to fresh values, as given by
    * nextArg.  Note: nextArg is not changed. */
  @inline def mapUndefinedToFresh(map: RemappingMap, nextArg: NextArgMap) = {
    for(t <- 0 until numTypes){
      var next = nextArg(t)
      for(i <- 0 until map(t).length)
        if(map(t)(i) < 0){ map(t)(i) = next; next += 1 }
    }
  }



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

  // /** Remap state st, returning its index; also update map and nextArg. */
  // @inline private 
  // def remapStateToIndex(map: RemappingMap, nextArg: NextArgMap, st: State)
  //     : StateIndex = {
  //   val remappedParams = remapParams(map, nextArg, st)
  //   MyStateMap.getByIndex(st.family, st.cs, remappedParams)
  // }

  /** Normalise st, returning the normalised version, and the total remapping
    * map used to produce it.  
    * @param types an array giving the types of the parameters. Note that we
    * can't use remapState here, because State.stateTypeMap hasn't been
    * initialised.  */
  def normaliseState(st: State, types: Array[Type]): (State, RemappingMap) = {
    val map = newRemappingMap; val nextArg = newNextArgMap
    val ids = st.ids; val len = ids.length; assert(types.length == len)
    val remappedParams = new Array[Identity](len); var index = 0
    // The domain and range of the parameters so far
    val dom, ran = Array.fill(numTypes)(List[Identity]())
    while(index < len){
      val t = types(index); val id = ids(index)
      val newInMap = id >= 0 && map(t)(id) < 0 // map gets extended below
      remappedParams(index) = remapArg(map, nextArg, t, id)
      if(newInMap){ 
        val newId = remappedParams(index); assert(map(t)(id) == newId)
        dom(t) ::= id; ran(t) ::= newId 
      }
      index += 1
    }
    val st1 = MyStateMap(st.family, st.cs, remappedParams)

    // Extend to have same domain and range
    for(t <- 0 until numTypes){
      // Add bijection from rdm to dmr
      var dmr = dom(t).diff(ran(t)); var rdm = ran(t).diff(dom(t))
      assert(dmr.length == rdm.length)
      while(dmr.nonEmpty){
        val x = dmr.head; val y = rdm.head; dmr = dmr.tail; rdm = rdm.tail
        assert(map(t)(y) < 0, show(map)+"\n"+s"$t ${dom(t)} ${ran(t)} $x");
        map(t)(y) = x
      }
      // Remap remainder under identity
      for(id <- 0 until map(t).length) if(map(t)(id) < 0) map(t)(id) = id
    }

    assert(isInjective(map))

    (st1, map)
  }

  /** Remap st to normalise it with respect to servers, cpts1, cpts2, i.e. using
    * the identity map over parameters of those, but otherwise mapping
    * parameters to the next fresh value. */
  def remapWRT(servers: ServerStates, cpts1: Array[State], cpts2: Array[State], 
    st: State)
      : State = {
    // Get upper bound on ids in servers, cpts1, cpts2
    val argBound = new Array[Identity](numTypes)
    /* Update argBound wrt st1. */
    @inline def update(st1: State) = 
      for((t,id) <- st1.processIdentities) argBound(t) = argBound(t) max (id+1)
    for(st1 <- servers.servers) update(st1)
    for(st1 <- cpts1) update(st1)
    for(st1 <- cpts2) update(st1)
    val nextArg = argBound.clone
    val map = newRemappingMap // IMPROVE: use Pools
    val newArgs = new Array[Identity](st.length)
    for(i <- 0 until st.length){
      val t = st.typeMap(i); val id = st.ids(i)
      if(id >= argBound(t)){
        if(map(t)(id) >= 0) newArgs(i) = map(t)(id)
        else{ map(t)(id) = nextArg(t); newArgs(i) = nextArg(t); nextArg(t) += 1 }
      }
      else newArgs(i) = id
    }
    MyStateMap(st.family, st.cs, newArgs)
  }

  /** Apply map to st; types gives the types. */
  def applyMap(st: State, map: RemappingMap, types: Array[Type]): State = {
    val ids = st.ids; val len = ids.length
    val remappedIds = new Array[Identity](len)
    for(i <- 0 until len){
      val id = ids(i); remappedIds(i) = if(id >= 0) map(types(i))(id) else id
    }
    MyStateMap(st.family, st.cs, remappedIds)
  }

  // ------ Remapping List[State] or  Views

  /** Remap procs, updating map and nextArg.  */
  @inline private def remapStates(
    map: RemappingMap, nextArg: NextArgMap, procs: List[State]): List[State] = 
    procs.map(st => remapState(map, nextArg, st))

  /** Remap procs, updating map and nextArg.  */
  @inline private def remapStates(
    map: RemappingMap, nextArg: NextArgMap, procs: Array[State]): Array[State] = 
    StateArray(procs.map(st => remapState(map, nextArg, st)))

  /** Cache used in remapServerStates. */
  private val remapSSCache = 
    new ShardedHashMap[ServerStates, (ServerStates, RemappingMap, NextArgMap)]

  /** Remap ss to normal form.  Also return resulting RemappingMap and
    * NextArgMap. */
  @inline private def remapServerStates(ss: ServerStates)
      : (ServerStates, RemappingMap, NextArgMap) = {
    def mkTuple: (ServerStates, RemappingMap, NextArgMap) = {
      val map0 = newRemappingMap; var nextArg = newNextArgMap
      val servers = ServerStates(remapStates(map0, nextArg, ss.servers))
      (servers, map0, nextArg)
    }
    val (servers, map, nextArgs) = remapSSCache.getOrElseUpdate(ss, mkTuple) 
    (servers, cloneMap(map), nextArgs.clone)
  }  

  // =================== Remapping views

  /** Remap a ComponentView. */
  @inline def remapView(v: ComponentView): ComponentView = {
    val (servers1, map, nextArg) = remapServerStates(v.servers)
    val components1 = remapStates(map, nextArg, v.components)
    Pools.returnRemappingRows(map)
    new ComponentView(servers1, components1) // principal1, others1)
  }

  /** Remap components so they are in normal form based on servers.  Pre:
    * servers are normalised. */
  @inline def remapComponents(servers: ServerStates, components: Array[State])
      : Array[State] = {
    val map = servers.remappingMap
    val res = remapStates(map, servers.nextArgMap, components)
    Pools.returnRemappingRows(map)
    res
  }

  /** Make a ComponentView from servers, principal and others, remapping to
    * canonical form. */
  @inline def mkComponentView(
    servers: ServerStates, components: Array[State]) = {
    // assert(components.forall(_ != null)) // IMPROVE
    val (servers1, map, nextArg) = remapServerStates(servers)
    val components1 = remapStates(map, nextArg, components)
    Pools.returnRemappingRows(map)
    new ComponentView(servers1, components1)
  }

  /** A ReducedComponentView containing servers and a remapped version of
    * components. */
  @inline def mkReducedComponentView(
    servers: ServerStates, components: Array[State]) = 
    ReducedComponentView(servers, remapComponents(servers, components))


  /** Is map defined over all the parameters of cpt? */
  def isDefinedOver(map: RemappingMap, cpt: State): Boolean = {
    val ids = cpt.ids; val len = ids.length; val typeMap = cpt.typeMap
    var i = 0; var ok = true
    while(i < len && ok){
      val id = ids(i)
      if(!isDistinguished(id) && map(typeMap(i))(id) < 0) ok = false
      i += 1
    }
    ok
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
    StateArray(result)
  }

  /** Remap st so that it can be the principal component in a view with
    * servers. */
  @inline def remapToPrincipal(servers: ServerStates, st: State): State = {
    // IMPROVE: could use a smaller remappingMap
    val map = servers.remappingMap
    val res = remapState(map, servers.nextArgMap, st)
    Pools.returnRemappingRows(map)
    res
  }
}
