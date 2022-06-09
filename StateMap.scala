package ViewAbstraction

import java.util.concurrent.atomic.{AtomicReferenceArray,AtomicIntegerArray}
// import ox.cads.util.Profiler

/** Trait for a map storing States, keyed by Family, ControlStates and
  * Identitys.  In addition (post-compilation), the States are stored in a
  * global array, and can be referenced by their indexes in that array, these
  * indices being guaranteed to be non-zero. */
trait StateMap{
  /** The number of elements in this. */
  def size: Int

  /** Get the State corresponding to (family, cs, ids), or create one if there
    * is no such. 
    * @param isNew is this being done during compilation?  If so, the ids 
    * are bound to be values from the script. */
  @inline def getOrAdd(family: Int, cs: ControlState, ids: Array[Identity])
      : State

  /** Get the State corresponding to (family, cs, ids), or create one if there
    * is no such.  Also return the index in the global array where the state
    * is stored (not during compilation).
    * @param isNew is this being done during compilation?  If so, the ids 
    * are bound to be values from the script. */
  @inline 
  def getOrAddByIndex(family: Int, cs: ControlState, ids: Array[Identity])
      : StateIndex 

  /** Add st to the store, or get the equivalent one if it exists. */
  // @inline def add(st: State): State

  /** The state in position ix of the global array. */
  def get(ix: Int) : State

}


// =======================================================

/*
NOT CURRENTLY USED
/** A thread-safe implementation of StateMap, using sharding. */
class ShardedStateMap(shards: Int = 128, initLength: Int = 16) 
    extends Sharding(shards) with StateMap{

  /** Array holding all states found so far.  Note: each state should be placed
    * in this array before being added to the relevant shard. */
  @volatile private var allStates = new Array[State](1024)
  
  /** The number of States stored in allStates. */
  private var allStatesCount = 0
  /* The states are held in allStates[1..allStatesCount). */

  /** Lock protecting allStates and allStatesCount. */
  private val allStatesLock = new AnyRef

  /** Store st in allStates, returning index used.  IMPROVE: make more
    * efficient. */
  @inline private 
  def addToArray(st: State): StateIndex = allStatesLock.synchronized{
    if(allStatesCount+1 == allStates.length){ // resize
      val newAllStates = new Array[State](2*allStates.length)
      for(i <- 1 to allStatesCount) newAllStates(i) = allStates(i)
      allStates = newAllStates
    }
    allStatesCount += 1; allStates(allStatesCount) = st
    allStates = allStates // volatile write; publish
    allStatesCount
  }

  def get(ix: Int): State = allStates(ix) // read of allStates is subscribe

  /** Maximum load factor before resizing. */
  private val MaxLoad = 0.7 // maps 16 -> 11

  // ========

  /** A single shard with n slots. */
  private class Shard(val n: Int){
    /** Bit mask to produce a value in [0..n). */
    private val mask = n-1

    /** The current number of entries. */
    var count = 0

    /** Threshold at which resizing should be performed. */
    private val threshold = (n*MaxLoad).toInt

    @inline def mustResize = count >= threshold

    /** The hashes of the mapping. */
    @volatile private var hashes = new Array[Int](n) // new AtomicIntegerArray(n)

    /** The control states. */
    private val controlStates = new Array[ControlState](n)

    /** The identites. */
    private val identities = new Array[Array[Identity]](n)

    /** The states. */
    val states = new Array[State](n)

    /* This represents { states(i) | i <- [0..n), hashes(i) != 0 }.  Each such
     * states(i) has control state controlStates(i) and identities
     * identities(i). */

    /** The indexes into the global array. */
    val indexes = new Array[StateIndex](n)
    /* For each states(i) in this shard, allStates(indexes(i)) = states(i). */

    /** Initialise this from oldShard. */
    def this(oldShard: Shard) = {
      this(oldShard.n*2); count = oldShard.count
      var j = 0 // index into old arrays
      while(j < oldShard.n){
        val h = oldShard.hashes/*.get*/(j)
        if(h != 0){
          var i = h&mask // index into new arrays
          while(hashes/*.get*/(i) != 0) i = (i+1) & mask
          controlStates(i) = oldShard.controlStates(j)
          identities(i) = oldShard.identities(j); states(i) = oldShard.states(j)
          indexes(i) = oldShard.indexes(j); hashes(i) = h // hashes.set(i, h)
        }
        j += 1
      }
    }

    /** Find the position at which element (cs,ids) with hash h is stored
      * or should be placed. */
    @inline def find(cs: ControlState, ids: Array[Identity], h: Int): Int = {
      var i = h & mask; var h1 = hashes/*.get*/(i)
      while(h1 != 0 &&
              (h1 != h || controlStates(i) != cs ||
                 ! identities(i).sameElements(ids))){
        i = (i+1) & mask; h1 = hashes/*.get*/(i) 
      }
      i
    }

    /** Add state st, corresponding to cs and ids, with hash h and global index
      * ix, in position i. */ 
    @inline def add(
      i: Int, cs: ControlState, ids: Array[Identity], newState: State, 
      ix: Int, h: Int) 
    = {
      // assert(states(i) == null && hashes.get(i) == 0) 
      controlStates(i) = cs; identities(i) = ids; states(i) = newState
      indexes(i) = ix; count += 1; hashes(i) = h // hashes.set(i, h)
      hashes = hashes // publish
    }
  } // end of Shard

  // ========

  /** The shards.  Each state in theShards(i) has hash h such that shardFor(h)
    * = i. */
  @volatile private var theShards = Array.fill(shards)(new Shard(initLength))

  private val locks = Array.fill(shards)(new AnyRef)

  private def getShard(sh: Int) = theShards(sh) 
    // volatile read of theShards; subscribe

  private def setShard(sh: Int, shard: Shard) = { 
    theShards(sh) = shard; theShards = theShards // volatile write; publish
  }

  /** Hash of x; guaranteed not to be 0. */
  @inline private def hashOf(cs: ControlState, ids: Array[Identity]) = {
    var h = cs; var i = 0; var n = ids.length
    while(i < n){ h = h*41+ids(i); i += 1 }
    h ^= ((h >>> 20) ^ (h >>> 12))
    h ^= (h >>> 7) ^ (h >>> 4)
    if(h == 0) 12344577 else h
  }

  // def add(st: State): State = ???

  /** Get or create new state corresponding to cs and ids, together with its
    * global index. */
  def getOrAddByIndex(family: Int, cs: ControlState, ids: Array[Identity])
      : StateIndex = {
    val h = hashOf(cs, ids); val sh = shardFor(h)
    getOrAddByIndex1(family, cs, ids, h, sh)
  }

  /** Helper function for getOrAddWithIndex. */
  @inline private def getOrAddByIndex1(
    family: Int, cs: ControlState, ids: Array[Identity], h: Int, sh: Int)
      : StateIndex = {
    // assert(!isNew)
    val shard = getShard(sh)
    val i = shard.find(cs, ids, h); val oldSt = shard.states(i)
    if(oldSt == null) locks(sh).synchronized{ // try to add
      if(getShard(sh) != shard || shard.states(i) != null)
        // An update has interfered with this; restart
        getOrAddByIndex1(family, cs, ids, h, sh)
      else if(shard.mustResize){
        val newShard = new Shard(shard); setShard(sh, newShard)
        getOrAddByIndex1(family, cs, ids, h, sh)
      }
      else{
        val newState = new State(family, cs, ids, false)
        val myIndex = addToArray(newState)
        shard.add(i, cs, ids, newState, myIndex, h)
        myIndex // (newState, myIndex)
      }
    } // end of synchronized block
    else{
      // assert(oldSt.cs == cs && oldSt.ids.sameElements(ids))
      // State.returnIdentityArray(ids) // recycle
      shard.indexes(i) // (oldSt, shard.indexes(i))
    }
  }

  /** Get or create new state corresponding to cs and ids. */
  def getOrAdd(family: Int, cs: ControlState, ids: Array[Identity])
      : State = {
    val h = hashOf(cs, ids); val sh = shardFor(h)
    getOrAdd1(family, cs, ids, h, sh) 
  }

  /** Helper function for getOrAdd. */
  @inline private def getOrAdd1(
    family: Int, cs: ControlState, ids: Array[Identity], h: Int, sh: Int)
      : State = {
    val shard = getShard(sh)
    val i = shard.find(cs, ids, h); val oldSt = shard.states(i)
    if(oldSt == null) locks(sh).synchronized{ // try to add
      if(getShard(sh) != shard || shard.states(i) != null)
        // An update has interfered with this; restart
        getOrAdd1(family, cs, ids, h, sh)
      else if(shard.mustResize){
        val newShard = new Shard(shard); setShard(sh, newShard)
        getOrAdd1(family, cs, ids, h, sh)
      }
      else{
        val newState = new State(family, cs, ids, false)
        val myIndex = addToArray(newState)
        shard.add(i, cs, ids, newState, myIndex, h)
        newState
      }
    } // end of synchronized block
    else{
      // assert(oldSt.cs == cs && oldSt.ids.sameElements(ids))
      // State.returnIdentityArray(ids) // recycle
      oldSt
    }
  }
  def size: Int = {
    var c = 0; for(sh <- theShards) c += sh.count; c
  }
}
 */
