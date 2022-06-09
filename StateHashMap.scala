package ViewAbstraction

/** A hash map storing States, keyed by ControlStates and Identitys.  This is
  * the base class of InitialisationStateHashMap. */
abstract class StateHashMap(initLength: Int) extends StateMap{
  // print("StateHashMap")
  // check initSize is a power of 2
  checkPow2(initLength)

  /** The current number of spaces in the table. */
  protected var n = initLength

  /** Bit mask to produce a value in [0..n). */
  protected var mask = n-1

  /** The current number of entries. */
  protected var count = 0

  /** The number of elements in this. */
  def size = count

  /** Maximum load factor before resizing. */
  private val MaxLoad = 0.5

  /** Threshold at which resizing should be performed. */
  protected var threshold = (initLength*MaxLoad).toInt

  /** The hashes of the mapping. */
  protected var hashes = new Array[Int](initLength)

  /** The control states. */
  protected var controlStates = new Array[ControlState](initLength)

  /** The identites. */
  protected var identities = new Array[Array[Identity]](initLength)

  /** The states. */
  protected var states = new Array[State](initLength)

  /** The indexes.  Null in InitialisationStateMap. */
  protected var indexes: Array[StateIndex]

  /** Hash of x; guaranteed not to be 0. */
  @inline protected def hashOf(cs: ControlState, ids: Array[Identity]) = {
    var h = cs; var i = 0; var n = ids.length
    while(i < n){ h = h*41+ids(i); i += 1 }
    h ^= ((h >>> 20) ^ (h >>> 12))
    h ^= (h >>> 7) ^ (h >>> 4)
    if(h == 0) 12344577 else h
  }

  /* This represents the mapping 
   * { (controlStates(i), identities(i)) -> states(i) | hashes(i) != 0 }.
   * 
   * Each element is placed in the first empty (null) position
   * starting from its hash.  Its hash is placed in the corresponding
   * position in hashes. */

  /** Resize the hash table. */
  @inline protected def resize() = {
    val oldN = n; n += n; threshold += threshold; mask = n-1
    // println("resize to "+n)
    val oldHashes = hashes; hashes = new Array[Int](n)
    val oldControlStates = controlStates
    controlStates = new Array[ControlState](n)
    val oldIdentities = identities; identities = new Array[Array[Identity]](n)
    val oldStates = states; states = new Array[State](n)
    // Resize indexes if not null
    val oldIndexes = indexes
    if(oldIndexes != null) indexes = new Array[StateIndex](n)
    var j = 0 // index into old arrays
    while(j < oldN){
      val h = oldHashes(j)
      if(h != 0){ // add old*(j) to new table
        var i = h & mask
        while(hashes(i) != 0) i = (i+1) & mask // (i+1)%n
        hashes(i) = h; controlStates(i) = oldControlStates(j)
        identities(i) = oldIdentities(j); states(i) = oldStates(j)
        if(indexes != null) indexes(i) = oldIndexes(j)
      }
      j += 1
    }
  }

  /** Find the position at which element (cs,ids) with hash h is stored
    * or should be placed. */
  @inline protected def find(cs: ControlState, ids: Array[Identity], h: Int)
      : Int = {
    var i = h & mask
    while(hashes(i) != 0 &&
            (hashes(i) != h || controlStates(i) != cs || 
               differentElements(identities(i), ids))){
      i = (i+1) & mask // = (i+1)%n
    }
    i
  }

  /** Do ids1 and ids2 have different elements?  
    * Pre: they have the same length. */
  @inline private 
  def differentElements(ids1: Array[Identity], ids2: Array[Identity]) 
      : Boolean = {
    var i = 0; val len = ids1.length
    while(i < len && ids1(i) == ids2(i)) i += 1
    i < len
  }

}

// =======================================================

/** A hash map storing States, keyed by ControlStates and Identitys. Not
  * thread safe.  Doesn't support the global array.   */
class InitialisationStateHashMap(initLength: Int = 4096) 
    extends StateHashMap(initLength){
  // println("InitialisationStateHashMap")

  /** Are we still compiling?  If so, States should be created with isNew = 
    * true. */
  private var isNew = true

  /** Record that compilation is over. */
  def doneCompiling = { println("Done compiling"); isNew = false }

  /** The indexes: null here. */
  protected var indexes: Array[StateIndex] = null

  /** Get the State corresponding to (cs, ids), or create one if there
    * is no such. */
  @inline def getOrAdd(family: Int, cs: ControlState, ids: Array[Identity])
      : State = {
    if(count >= threshold) resize()
    val h = hashOf(cs, ids); val i = find(cs, ids, h); val oldSt = states(i)
    if(oldSt == null){
      // assert(hashes(i) == 0 && states(i) == null)
      hashes(i) = h; controlStates(i) = cs; identities(i) = ids
      val newState = new State(family, cs, ids, isNew); states(i) = newState
      count += 1; newState
    }
    else{
      // assert(oldSt.cs == cs && oldSt.ids.sameElements(ids));
      oldSt
    }
  }  

  // The following two methods aren't needed during initialisation. 

  def getOrAddByIndex(family: Int, cs: ControlState, ids: Array[Identity]) = ???
   // getOrAddWithIndex(family, cs, ids, isNew)._2

  /** The state in position ix of the global array. */
  def get(ix: Int) : State = ???

  /** An iterator over the states. */
  def iterator = new Iterator[State]{
    /** Index of the next element. */
    private var i = 0

    advance

    /** Advance i to next element. */
    private def advance = while(i < n && hashes(i) == 0) i += 1

    /** Does the iterator have a next element? */
    def hasNext = i < n

    /** The next element of the iterator. */
    def next() = { val result = states(i); i += 1; advance; result }    
  } // end of iterator

  /** Create an Array holding all the states.  Not currently used. */
  def toArray: Array[State] = {
    // build up result in ab
    val ab = new scala.collection.mutable.ArrayBuffer[State]; var i = 0
    while(i < n){
      while(i < n && hashes(i) == 0) i += 1
      if(i < n){ ab += states(i); i += 1 }
    }
    ab.toArray
  }

}

// =======================================================

/* 
NOT CURRENTLY USED
/** A thread-local StateMap, with access to a shared state map, trieStateMap.
  * The shared state map is used for obtaining States that are new to the
  * current thread; these are then cached in this object. 
  * 
  * Unfortunately, this seems less efficient than a raw MyTrieStateMap. */
class ThreadLocalStateHashMap(trieStateMap: MyTrieStateMap)
    extends StateHashMap(4096){ // IMPROVE: initial size??
  protected var indexes = new Array[StateIndex](4096)

  def get(ix: Int): State = ???

  @noinline def getOrAdd(
    family: Int, cs: ControlState, ids: Array[Identity])
      : State = {
    // assert(!isNew)
    if(count >= threshold) resize()
    val h = hashOf(cs, ids); val i = find(cs, ids, h); val oldSt = states(i)
    if(oldSt == null){ makeNew(i, family, cs, ids, h); states(i) }
    else oldSt
  }

  /** Get a new state from trieStateMap, possibly creating it there, and copying
    * it into this object. */
  @inline private def makeNew(
    i: Int, family: Int, cs: ControlState, ids: Array[Identity], h: Int)
  = {
    hashes(i) = h; controlStates(i) = cs; identities(i) = ids
    val (newState, newIndex) =
      trieStateMap.getOrAddWithIndex(family, cs, ids)
    states(i) = newState; indexes(i) = newIndex; count += 1
  }

  @noinline def getOrAddByIndex(family: Int, cs: ControlState, ids: Array[Identity])
      : StateIndex = {
    // assert(!isNew)
    if(count >= threshold) resize()
    val h = hashOf(cs, ids); val i = find(cs, ids, h)
    if(states(i) == null) makeNew(i, family, cs, ids, h)
    indexes(i)
  }

  /** Add st with index index.  Used in initialisation. */
  def add(st: State, index: StateIndex) = {
    if(count >= threshold) resize()
    val cs = st.cs; val ids = st.ids
    val h = hashOf(cs, ids); val i = find(cs, ids, h); assert(states(i) == null)
    hashes(i) = h; controlStates(i) = cs; identities(i) = ids
    states(i) = st; count += 1; indexes(i) = index
  }

  override def clone: ThreadLocalStateHashMap = {
    val that = new ThreadLocalStateHashMap(trieStateMap)
    that.n = n; that.mask = mask; that.count = count; that.threshold = threshold
    that.hashes = hashes.clone; that.controlStates = controlStates.clone
    that.identities = identities.clone; that.states = states.clone
    that.indexes = indexes.clone; that
  }
}

// =======================================================

/** A StateMap where each thread has its own ThreadLocalStatehashMap map,
  * cloned from template; and they share a MyTrieStateMap, trieStateMap. */
class ThreadLocalStateHashMaps(
  template: ThreadLocalStateHashMap, trieStateMap: MyTrieStateMap)
    extends StateMap{

  /** The ThreadLocalStateHashMaps. */
  private object Maps extends ThreadLocal[ThreadLocalStateHashMap]{
    override def initialValue() = template.clone
  }  

  /* The first two operations are delegated to the trieStateMap. */

  @noinline def get(ix: Int): State = trieStateMap.get(ix)

  def size: Int = trieStateMap.size

  /* The other two operations are delegated to the thread-local maps. */

  @noinline def getOrAdd(family: Int, cs: ControlState, ids: Array[Identity]): State = 
    Maps.get.getOrAdd(family, cs, ids)

  @noinline def getOrAddByIndex(family: Int, cs: ControlState, ids: Array[Identity])
      : StateIndex = 
    Maps.get.getOrAddByIndex(family, cs, ids)
}

// IMPROVE: inline throughout
 */
