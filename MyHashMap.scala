package ViewAbstraction

/** A HashMap, mapping from A to B. */
trait MyHashMap[A,B]{
  /** Get the value associated with a, if one exits; otherwise update it
    * to the value of b. */
  def getOrElseUpdate(a: A, b: => B): B

  def size: Int

  def apply(a: A): B
}

// =======================================================

import scala.collection.mutable.Map

// class SimpleHashMap[A,B] extends MyHashMap[A,B]{
//   /** The underlying map. */
//   private val underlying = Map[A,B]()

//   /** Get the value associated with a, if one exits; otherwise update it
//     * to the value of b. */
//   def getOrElseUpdate(a: A, b: => B): B =
//     synchronized{ underlying.getOrElseUpdate(a, b) }

//   def size = underlying.size
// }

// =======================================================

/** An implementation of MyHashMap using a sharded hash table with
  * open addressing. 
  * @param shards the number of shards
  * @param initLength the initial length of each shard. */
// class ShardedHashMap[A: scala.reflect.ClassTag, B: scala.reflect.ClassTag](
//   shards: Int = 128, initLength: Int = 32)
//     extends MyHashMap[A,B]{

//   checkPow2(initLength)

//   /* We use a two-dimensional array, of size shards, with each row s
//    * having width widths(s), to store states.  Inv: widths(s) is a
//    * power of 2, widths(s) <= MaxWidth. */

//   /** The number of entries in each shard. */
//   private var widths: Array[Int] = Array.fill(shards)(initLength)

//   /** Array holding the keys of the map. */
//   private val keys = Array.fill(shards)(new Array[A](initLength))

//   /** Array holding the elements of the set. */
//   private var elements = Array.fill(shards)(new Array[B](initLength))

//   /** The hashes of the set. */
//   private var hashes = Array.fill(shards)(new Array[Int](initLength))

//   /** The current number of entries in each shard. */
//   private var counts = new Array[Int](shards)

//   /** Bit mask to produce a value in [0..width).  Inv: for each sh,
//     * widthMasks(sh) = widths(sh)-1. */
//   private var widthMasks = Array.fill(shards)(initLength-1)

//   /** Maximum load factor before resizing. */
//   private val MaxLoad = 0.5

//    /** Threshold at which resizing should be performed. */
//   private val thresholds = Array.fill(shards)((initLength*MaxLoad).toInt)

//   /** Locks: locks(s) protects shard(s). */
//   private val locks = Array.fill(shards)(new AnyRef)

//   /** Bit shift to produce a value in [0..shards).  */
//   private var shardShift = {
//     var s = shards; var ss = 0 // Inv shards = s * 2^ss
//     while(s > 1){
//       assert((s&1) == 0); s = s >>> 1; ss += 1
//     }
//     32-ss
//   }
//   println("shardShift = "+shardShift)

//   /** The shard to use for a value with hash h; the most significant
//     * bits of h. */
//   @inline private def shardFor(h: Int) = h >>> shardShift

//   /** The entry in shard sh = shardFor(h) in which a value with hash h
//     * should be placed. */
//   @inline private def entryFor(sh: Int, h: Int): Int = h & widthMasks(sh)

//   /* An element with hash h is placed in shard sh = shardFor(h), in the
//    * first empty (null) position in keys(sh) and elements(sh), starting
//    * from position entryFor(sh, h), wrapping round.  Its hash h is
//    * placed in the corresponding position in hashes.  Note that we
//    * wrap around in the same shard, rather than moving onto the next
//    * shard.  */

//   /** The number of elements in this. */
//   def size: Int = counts.sum

//   /** Find the position at which element x with hash h is stored or should be
//     * placed. */
//   @noinline private def find(sh: Int, x: A, h: Int): Int = {
//     var i = entryFor(sh, h)
//     assert(i < widths(sh))
//     while(hashes(sh)(i) != 0 && (hashes(sh)(i) != h || keys(sh)(i) != x))
//       i = (i+1) & widthMasks(sh)
//     i
//   }

//   /** Get the value associated with a, if one exits; otherwise update it
//     * to the value of b. */
//   def getOrElseUpdate(a: A, b: => B): B = {
//     val h = hashOf(a); val sh = shardFor(h)
//     locks(sh).synchronized{
//       if(counts(sh) >= thresholds(sh)) resize(sh)
//       // Find empty slot or slot containing x
//       val i = find(sh, a, h)
//       if(hashes(sh)(i) == h){ /* assert(keys(sh)(i) == a); */ elements(sh)(i) }
//       else{
//         // println("Adding "+a+" -> "+b)
//         assert(hashes(sh)(i) == 0 && keys(sh)(i) == null &&
//                  elements(sh)(i) == null)
//         hashes(sh)(i) = h; keys(sh)(i) = a; val myB = b; elements(sh)(i) = myB
//         counts(sh) += 1; myB
//       }
//     }
//   }

//   /** Resize shard sh of the hash table. */
//   @inline private def resize(sh: Int) = {
//     // Increase width of shard sh
//     val oldWidth = widths(sh); val newWidth = 2*oldWidth
//     widths(sh) = newWidth; val mask = newWidth-1; widthMasks(sh) = mask
//     thresholds(sh) += thresholds(sh)
//     println("Resizing hash map "+sh+" to"+newWidth)
//     // Create new arrays
//     val oldHashes = hashes(sh); hashes(sh) = new Array[Int](newWidth)
//     val oldElements = elements(sh); elements(sh) = new Array[B](newWidth)
//     val oldKeys = keys(sh); keys(sh) = new Array[A](newWidth)
//     // Copy elements
//     var i = 0  //  index into oldHashes, oldElements
//     while(i < oldWidth){
//       val h = oldHashes(i)
//       if(h != 0){ // add oldElements(i) to new table
//         var i1 = entryFor(sh, h)
//         while(hashes(sh)(i1) != 0) i1 = (i1+1) & mask
//         hashes(sh)(i1) = h
//         assert(elements(sh)(i1) == null)
//         elements(sh)(i1) = oldElements(i)
//       }
//       i += 1
//     }
//   }
// }

// =======================================================

/** An implementation of MyHashMap that provides lock-free reads of
  * existing values.  This is designed to give good performance when
  * new values are quite rare. */
class MyLockFreeReadHashMap
  [A: scala.reflect.ClassTag, B: scala.reflect.ClassTag](initLength: Int = 64)
    extends MyHashMap[A,B]{

  checkPow2(initLength)

  /** Maximum load factor before resizing. */
  private val MaxLoad = 0.5

  /** Objects encapsulating the state. */
  private class TableState(val n: Int){
    /** The hashes of the mapping. */
    val hashes = new java.util.concurrent.atomic.AtomicIntegerArray(n)

    /** The states of the individual servers. */
    val keys = new Array[A](n)

    /** The corresponding ServerState objects. */
    val values = new Array[B](n)

    /** Bit mask to produce a value in [0..n). */
    val mask = n-1

    /** Find the position at which element (cs,ids) with hash h is stored
      * or should be placed. */
    @inline def find(a: A, h: Int) : Int = {
      var i = h & mask
      while({ val h1 = hashes.get(i); h1 != 0 && (h1 != h || keys(i) != a) })
        i = (i+1) & mask // (i+1)%n
      i
    }

    /* This represents the mapping
     * { keys(i) -> values(i) | hashes(i) != 0 }.
     * 
     * Each element is placed in the first empty (null) position
     * starting from its hash.  Its hash is placed in the
     * corresponding position in hashes.  Each entry is published when
     * its hash is written. */
  }

  /** The state of the table. */
  @volatile private var state = new TableState(initLength)

  /** The current number of entries. */
  private var count = 0

  /** The number of elements in this. */
  def size = count

  /** Threshold at which resizing should be performed. */
  private var threshold = (initLength*MaxLoad).toInt

  /** Resize the hash table. */
  @inline private def resize(oldState: TableState): TableState = {
    val oldN = oldState.n; val newState = new TableState(oldN*2)
    // println("ServerStates resize to "+oldN*2)
    threshold = 2*threshold
    val mask = newState.mask; var j = 0 // index into old arrays
    while(j < oldN){
      val h = oldState.hashes.get(j)
      if(h != 0){ // add oldState._(j) entries to new table
        var i = h & mask
        while(newState.hashes.get(i) != 0) i = (i+1) & mask 
        newState.keys(i) = oldState.keys(j)
        newState.values(i) = oldState.values(j)
        newState.hashes.set(i, h)
      }
      j += 1
    }
    state = newState // publish new state
    newState
  }

  /** Get the value associated with a, if one exits; otherwise update it
    * to the value of b. */
  def getOrElseUpdate(a: A, b: => B): B = {
    val h = hashOf(a); var myState = state // volatile read: subscribe
    var i = myState.find(a, h); val oldObj = myState.values(i)
    if(oldObj == null) synchronized{
      // Check state unchanged and no other thread wrote to i
      if(myState != state || myState.hashes.get(i) != 0)
        getOrElseUpdate(a, b) // retry
      else{
        if(count >= threshold){
          myState = resize(myState); i = myState.find(a, h)
        }
        // Store new ServerStates in position i
        // assert(myState.hashes.get(i) == 0 && myState.keys(i) == null)
        myState.keys(i) = a; val newObj = b; myState.values(i) = newObj
        myState.hashes.set(i, h) // publish update
        count += 1; newObj
      }
    } // end of synchronized block
    else if(myState.keys(i) == a) oldObj
    else getOrElseUpdate(a, b) // slot taken by another op; retry
  }

  /** Get the value associated with a.  Pre: such a value exists. */
  def apply(a: A): B = {
    val h = hashOf(a); var myState = state // volatile read: subscribe
    var i = myState.find(a, h); myState.values(i)
    // assert(b != null, "MyHashMap: key not found: "+a); b
  }
}
