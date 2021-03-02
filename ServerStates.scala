package ViewAbstraction

/** The states of the servers within a SystemView. */
class ServerStates(val servers: List[State]){
  /* Note: equality is reference equality, because we avoid creating two
   * ServerStates with the same value of servers. */

  /** Create hash code. */
  @inline private def mkHash: Int = {
    var h = 0
    for(st <- servers) h = h*73 + st.hashCode
    h
  }

  /** Override hash function. */
  override val hashCode = mkHash
  
  /** For each type t, the list of identities of type t used within servers. */
  val serverIds: Array[List[Identity]] = mkServerIds

  /** Is this normalised? */
  private var normalised = true

  /** Initialise serverIds */
  private def mkServerIds = {
    val result = Array.fill(numTypes)(List[Identity]())
    for(st <- servers){
      var index = 0
      for(id <- st.ids){
        val t = State.stateTypeMap(st.cs)(index); index += 1
        if(!isDistinguished(id) && !result(t).contains(id)){
          if(result(t).isEmpty) normalised &&= id == 0
          else normalised &&= id == result(t).head+1
          result(t) ::= id
        }
      }
    }
    result
  }

  /** Number of parameters of each type. */
  val numParams = serverIds.map(_.length)

  /** Bitmap showing which identities are included in this. */
  // val serverIdsBitMap = 
  //   if(normalised)
  //     Array.tabulate(numTypes)(t =>
  //       Array.tabulate(State.rowSizes(t))(i => i < numParams(t)))
  //   else null

  /** A template Remapper.RemappingMap */
  private val remappingMapTemplate = Array.tabulate(numTypes)(t => 
    Array.tabulate(State.rowSizes(t))(i => if(i < numParams(t)) i else -1))

  def remappingMap: Array[Array[Identity]] = {
    assert(normalised)
    val result = new Array[Array[Identity]](numTypes); var t = 0
    while(t < numTypes){ result(t) = remappingMapTemplate(t).clone; t += 1 }
    result
    // Array.tabulate(numTypes)(t => remappingMapTemplate(t))
  }

  def nextArgMap = { assert(normalised); numParams.clone }

  /** Identity mapping on identities held by servers, for each type. */
  val rhoS: ParamMap = 
    Array.tabulate(numTypes){t => val ids = serverIds(t); ids.zip(ids) }

  override def toString = servers.mkString("[", " || ", "]")
}

// =======================================================


/** Companion object. */
object ServerStates{
  /** Map containing all ServerStates objects created so far. */
  private val ssMap = new MyLockFreeReadHashMap[List[State], ServerStates]
  // private val ssMap: ServerStatesMap = new ServerStatesLockFreeReadHashMap
    // new ServerStatesHashMap

  /** The number of ServerStates objects created so far. */
  def count = ssMap.size

  /** Factory method. */
  def apply(servers: List[State]): ServerStates = {
    // count += 1; new ServerStates(servers)
    // ssMap.getOrAdd(servers)
    ssMap.getOrElseUpdate(servers, new ServerStates(servers))
  }
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
