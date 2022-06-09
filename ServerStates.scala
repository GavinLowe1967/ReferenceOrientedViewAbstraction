package ViewAbstraction
import ox.gavin.profiling.Profiler

/** The states of the servers within a SystemView. */
class ServerStates(val servers: List[State]){
  val index = ServerStates.getNextIndex

  /* Note: equality is reference equality, because we avoid creating two
   * ServerStates with the same value of servers. */

  /** Override hash function. */
  override val hashCode = {
    var h = 0
    for(st <- servers) h = h*73 + st.hashCode
    h
  } 
  
  /** Is this normalised? */
  private var normalised = true

  def isNormalised = normalised

  /** The parameters used in this, as a bit map. */
  val idsBitMap = newBitMap

  /** Upper bound on the parameter of each type: all parameters (t,p) have p <
    * paramsBound(t), and the bound is tight. */
  val paramsBound = new Array[Int](numTypes) 

  // def getParamsBound = paramsBound.clone

  /** Initialise serverIdsBitMap, normalised, numParams, paramsBound. */
  private def mkParamsInfo() = {
    // Traverse parameters, updating information
    for(st <- servers){
      var index = 0
      // for(id <- st.ids){
      while(index < st.ids.length){
        val id = st.ids(index)
        val t = State.stateTypeMap(st.cs)(index); index += 1
        if(!isDistinguished(id) && !idsBitMap(t)(id)){
          normalised &&= id == paramsBound(t)
          idsBitMap(t)(id) = true; paramsBound(t) = paramsBound(t) max (id+1)
        }
      }
    }
    if(normalised) for(t <- 0 until numTypes) 
      assert(paramsBound(t) == idsBitMap(t).count(_ == true))
  }

  mkParamsInfo()

  /** A template Remapper.RemappingMap */
  private val remappingMapTemplate = 
    if(normalised)
      Array.tabulate(numTypes)(t =>
        // For a remapping involving this, assuming the script has enough
        // parameters, each set of components can have at most
        // typeSizes(t)-paramsBound(t) fresh parameters, giving the value below.
        Array.tabulate(2*typeSizes(t)-paramsBound(t))(i =>
          if(i < paramsBound(t)) i else -1))
    else null

  /** A (fresh) RemappingMap, representing the identity on the parameters of 
    * this; or null if this is not normalised. */
  def remappingMap: RemappingMap = {
    if(!normalised) null
    else{
      val result = new Array[Array[Identity]](numTypes); var t = 0
      while(t < numTypes){ result(t) = remappingMapTemplate(t).clone; t += 1 }
      result
    }
  }

  /** A (fresh) RemappingMap, of size `size(t)` for each t, representing the
    * identity on the parameters of this. 
    * 
    * Note: client code should use at most one such map at a time.  It is
    * called from SingleRefEffectOnUnification.apply and
    * EffectOnUnification.apply. */
  def remappingMap1(size: Array[Int]): RemappingMap = {
    //Profiler.count("ServerStates.remappingMap1")
    require(normalised)
    // Note: we aim to do no new memory allocation here.
    val result = ServerStates.remappingMapStore; var t = 0
    // val result = new Array[Array[Identity]](numTypes); var t = 0
    while(t < numTypes){
      result(t) = ServerStates.getRemappingMapRow(t, size(t)) 
      // new Array[Identity](size(t))
      var i = 0
      while(i < paramsBound(t)){ result(t)(i) = i; i += 1 }
      while(i < size(t)){ result(t)(i) = -1; i += 1 }
      //  result(t)(i) = (if(i < paramsBound(t)) i else -1); i += 1
      t += 1
    }
    result
  }

  def nextArgMap = { assert(normalised); paramsBound.clone }

  def nextArgMap1 = paramsBound.clone

  /** Is this representable using the values defined in the script? */
  val representableInScript = servers.forall(_.representableInScript)

  override def toString = servers.mkString("[", " || ", "]")

  /** Convert to string, safe version. */
  def toString0 = servers.map(_.toString0).mkString("[", " || ", "]")

  /** Ordering on ServerStates values.  Return a value x s.t.: x < 0 if this <
    * that; x == 0 when this == that; x > 0 when this > that. */
  def compare(that: ServerStates) = {
    val hashComp = compareHash(hashCode, that.hashCode)
    if(hashComp != 0) hashComp
    else if(this == that) 0
    else{
      var i = 0
      while(servers(i) != that.servers(i)) i += 1
      servers(i).compare(that.servers(i))
    }
  }
}

// =======================================================


/** Companion object. */
object ServerStates{
  /** Map containing all ServerStates objects created so far. */
  private val ssMap = new MyLockFreeReadHashMap[List[State], ServerStates]
  // private val ssMap: ServerStatesMap = new ServerStatesLockFreeReadHashMap

  /** Index of the next ServerStates to create. */
  private var nextIndex = 0

  /** Get the index for the next ServerStates to create. */
  private def getNextIndex: Int = synchronized{ nextIndex += 1; nextIndex-1 }

  /** The number of ServerStates objects created so far. */
  def count = { assert(nextIndex == ssMap.size); nextIndex }

  /** Factory method. */
  def apply(servers: List[State]): ServerStates = {
    ssMap.getOrElseUpdate(servers, new ServerStates(servers))
  }

  /** All the new parameters in post, but not in pre, as a bit map. */
  def newParamsBitMap(pre: ServerStates, post: ServerStates)
      : Array[Array[Boolean]] = {
    require(pre.isNormalised)
    //Profiler.count("ServerStates.newParamsBitMap:newBitMap")
    val newIds = newBitMap; var sts: List[State] = post.servers
    while(sts.nonEmpty){
      val pids = sts.head.processIdentities; sts = sts.tail; var i = 0
      while(i < pids.length){
        val (f,id) = pids(i); i += 1
        if(id >= pre.paramsBound(f)) newIds(f)(id) = true
      }
    }
    newIds
  }

  /** A store for rows of RemappingMaps, used in remappingMap1(size).
    * remappingMapStore(t)(size) holds an array that can be used for row t of
    * size size of a RemappingMap.  These are initialised on demand.
    * 
    * Note: each should be used in only one way at a time.  In a concurrent
    * implementation, these would need to be thread-local. */
  private[this] val remappingMapRowStore = 
    if(false)
      Array.tabulate(numTypes)(t => new Array[Array[Int]](2*typeSizes(t)))
    else null 

  /** Get a rows of a RemappingMap, for type t and size size. 
    * 
    * Note: each result should be used in only one way at a time.  */
  private def getRemappingMapRow(t: Int, size: Int) = 
  if(false){
    if(remappingMapRowStore(t)(size) == null)
      remappingMapRowStore(t)(size) = new Array[Identity](size)
    remappingMapRowStore(t)(size)
  }
  else new Array[Identity](size)
  // IMPROVE: reuse

  /** A RemappingMap, used in remappingMap1(size).
    * 
    * Note: this should be used in only one way at a time.  In a concurrent
    * implementation, these would need to be thread-local. */
  private def remappingMapStore = new Array[Array[Identity]](numTypes)
  // IMPROVE: reuse
}

// =======================================================

// import ox.cads.util.Profiler

// trait ServerStatesMap{
//   def getOrAdd(ss: List[State]): ServerStates

//   def size: Int

//   /** Hash of ss; guaranteed not to be 0. */
//   @inline protected def hashOf(ss: List[State]) = {
//     var h = 0
//     for(st <- ss) h = h*73 + st.hashCode
//     h ^= ((h >>> 20) ^ (h >>> 12))
//     h ^= (h >>> 7) ^ (h >>> 4)
//     if(h == 0) 12344577 else h
//   }

//   /** Check initLength is a power of 2. */
//   protected def checkLen(initLength: Int) = {
//     var len = initLength
//     while(len > 1){
//       assert((len&1) == 0, "ServerStatesMap: initial size not a power of 2")
//       len = len >>> 1
//     }
//   }
// }

// // =======================================================

// /** A hash map storing ServerStates, keyed by the corresponding List
//   * of State.  */
// class ServerStatesHashMap(initLength: Int = 4096) extends ServerStatesMap{
//   checkLen(initLength)

//   /** The current number of spaces in the table. */
//   private var n = initLength

//   /** Bit mask to produce a value in [0..n). */
//   private var mask = n-1

//   /** The current number of entries. */
//   private var count = 0

//   /** The number of elements in this. */
//   def size = count

//   /** Maximum load factor before resizing. */
//   private val MaxLoad = 0.5

//   /** Threshold at which resizing should be performed. */
//   private var threshold = (initLength*MaxLoad).toInt

//   /** The hashes of the mapping. */
//   private var hashes = new Array[Int](initLength)

//   /** The states of the individual servers. */
//   private var servers = new Array[List[State]](initLength)

//   /** The corresponding ServerState objects. */
//   private var ssObjects = new Array[ServerStates](initLength)

//   /* This represents the mapping 
//    * { servers(i) -> ssObjects(i) | hashes(i) != 0 }.
//    * 
//    * Each element is placed in the first empty (null) position
//    * starting from its hash.  Its hash is placed in the corresponding
//    * position in hashes. */

//   /** Resize the hash table. */
//   @inline private def resize() = {
//     val oldN = n; n += n; threshold += threshold; mask = n-1
//     // println("resize to "+n)
//     val oldHashes = hashes; hashes = new Array[Int](n)
//     val oldServers = servers; servers = new Array[List[State]](n)
//     val oldSSObjects = ssObjects; ssObjects = new Array[ServerStates](n)
//     var j = 0 // index into old arrays
//     while(j < oldN){
//       val h = oldHashes(j)
//       if(h != 0){ // add old*(j) to new table
//         var i = h & mask
//         while(hashes(i) != 0) i = (i+1) & mask // (i+1)%n
//         hashes(i) = h; servers(i) = oldServers(j)
//         ssObjects(i) = oldSSObjects(j)
//       }
//       j += 1
//     }
//   }

//   /** Find the position at which element (cs,ids) with hash h is stored
//     * or should be placed. */
//   @inline private def find(ss: List[State], h: Int) : Int = {
//     var i = h & mask
//     while(hashes(i) != 0 && (hashes(i) != h || servers(i) != ss))
//       i = (i+1) & mask // (i+1)%n
//     i
//   }

//   /** Get the ServerStates corresponding to ss, or create one if there
//     * is no such. */
//   @inline def getOrAdd(ss: List[State]): ServerStates = synchronized{
//     // Profiler.count("getOrAdd")
//     if(count >= threshold) resize()
//     val h = hashOf(ss); val i = find(ss, h); val oldObj = ssObjects(i)
//     if(oldObj == null){
//       assert(hashes(i) == 0 && servers(i) == null)
//       hashes(i) = h; servers(i) = ss
//       val newObj = new ServerStates(ss); ssObjects(i) = newObj
//       count += 1; newObj
//     }
//     else{ assert(oldObj.servers == ss); oldObj }
//   }

// }

// // =======================================================

// /** An implementation of ServerStatesMap proving lock-free reads of
//   * existing values. */
// class ServerStatesLockFreeReadHashMap(initLength: Int = 64)
//     extends ServerStatesMap{
//   checkLen(initLength)

//   /** Maximum load factor before resizing. */
//   private val MaxLoad = 0.5

//   /** Objects encapsulating the state. */
//   private class TableState(val n: Int){
//     /** The hashes of the mapping. */
//     var hashes = new java.util.concurrent.atomic.AtomicIntegerArray(n)

//     /** The states of the individual servers. */
//     var servers = new Array[List[State]](n)

//     /** The corresponding ServerState objects. */
//     var ssObjects = new Array[ServerStates](n)

//     /** Bit mask to produce a value in [0..n). */
//     val mask = n-1

//     /** Find the position at which element (cs,ids) with hash h is stored
//       * or should be placed. */
//     @inline def find(ss: List[State], h: Int) : Int = {
//       var i = h & mask
//       while({ val h1 = hashes.get(i); h1 != 0 && (h1 != h || servers(i) != ss) })
//         i = (i+1) & mask // (i+1)%n
//       i
//     }

//     /* This represents the mapping
//      * { servers(i) -> ssObjects(i) | hashes(i) != 0 }.
//      * 
//      * Each element is placed in the first empty (null) position
//      * starting from its hash.  Its hash is placed in the
//      * corresponding position in hashes.  Each entry is published when
//      * its hash is written. */
//   }

//   /** The state of the table. */
//   @volatile private var state = new TableState(initLength)

//   /** The current number of entries. */
//   private var count = 0

//   /** The number of elements in this. */
//   def size = count

//   /** Threshold at which resizing should be performed. */
//   private var threshold = (initLength*MaxLoad).toInt

//   /** Resize the hash table. */
//   @inline private def resize(oldState: TableState): TableState = {
//     val oldN = oldState.n; val newState = new TableState(oldN*2)
//     println("ServerStates resize to "+oldN*2)
//     threshold = 2*threshold
//     val mask = newState.mask; var j = 0 // index into old arrays
//     while(j < oldN){
//       val h = oldState.hashes.get(j)
//       if(h != 0){ // add oldState._(j) entries to new table
//         var i = h & mask
//         while(newState.hashes.get(i) != 0) i = (i+1) & mask 
//         newState.servers(i) = oldState.servers(j)
//         newState.ssObjects(i) = oldState.ssObjects(j)
//         newState.hashes.set(i, h)
//       }
//       j += 1
//     }
//     state = newState // publish new state
//     newState
//   }


//   /** Get the ServerStates corresponding to ss, or create one if there
//     * is no such. */
//   @inline def getOrAdd(ss: List[State]): ServerStates = {
//     val h = hashOf(ss); var myState = state // volatile read: subscribe
//     var i = myState.find(ss, h); val oldObj = myState.ssObjects(i)
//     if(oldObj == null) synchronized{
//       // Check state unchanged and no other thread wrote to i
//       if(myState != state || myState.hashes.get(i) != 0) getOrAdd(ss) // retry
//       else{
//         if(count >= threshold){
//           myState = resize(myState); i = myState.find(ss, h)
//         }
//         // Store new ServerStates in position i
//         assert(myState.hashes.get(i) == 0 && myState.servers(i) == null)
//         myState.servers(i) = ss
//         val newObj = new ServerStates(ss); myState.ssObjects(i) = newObj
//         myState.hashes.set(i, h) // publish update
//         count += 1; newObj
//       }
//     } // end of synchronized block
//     else{ assert(oldObj.servers == ss); oldObj }
//   }

// }
