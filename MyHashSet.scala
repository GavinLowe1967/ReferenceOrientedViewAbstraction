package ViewAbstraction

// import ox.cads.util.Profiler

/** A HashSet containing data of type A. */
trait MyHashSet[A]{
  /** The number of elements in this. */
  def size: Long

  /** Summary of sizes. */
  def reportSizes: Array[Long] = Array(size)

  /** Add x to the set.
    * @return true if x was not previously in the set. */
  def add(x: A): Boolean

  /** An iterator over the elements of this.
    * Not thread safe. */
  def iterator: Iterator[A]

  /** Get the element of this that is equal (==) to x. 
    * Pre: such an element exists; and this operation is not concurrent with
    * any add operation. */
  def get(x: A): A

  /** Get the element of this that is equal (==) to x, or add x if there
    * is no such. */
  // def getOrAdd(x: A): A 

  def apply(x: A) = contains(x)

  /** Does this contain x?
    *  Pre: this operation is not concurrent to any add operation. */
  def contains(x: A): Boolean
}

// ==================================================================

/** A basic implementation of a hash map, using open addressing. */
class BasicHashSet[A: scala.reflect.ClassTag](initSize: Int = 16)
    extends MyHashSet[A]{

  checkPow2(initSize)

  /** The number of keys. */
  private var count = 0L

 /** The number of slots in the hash table. */
  private var n = initSize

  /** A bitmask to produce a value in [0..n). */
  private var mask = n-1

  /** The threshold ratio at which resizing happens. */
  private val ThresholdRatio = 0.6

  /** The threshold at which the next resizing will happen. */
  private var threshold = initSize * ThresholdRatio

  /** The array holding the keys. */
  private var keys = new Array[A](initSize)

  /** Find the index in the arrays corresponding to k. */
  private def find(k: A): Int = {
    var i = k.hashCode & mask
    while(keys(i) != k && keys(i) != null) i = (i+1)&mask
    i
  }  

  /** Add x to this set. */
  def add(x: A): Boolean = {
    val i = find(x)
    if(keys(i) == null){
      if(count >= threshold){ resize(); return add(x) }
      keys(i) = x; count += 1; true
    }
    else false
  }

  /** Resize the hash table. */
  private def resize(): Unit = {
    val oldKeys = keys; val oldN = n
    n += n; threshold = n * ThresholdRatio; mask = n-1
    keys = new Array[A](n); var i = 0
    while(i < oldN){
      val k = oldKeys(i)
      if(k != null){ // copy across
        val j = find(k); keys(j) = k
      }
      i += 1
    }
  }

  /** An iterator over the values in the set. */
  def iterator = new Iterator[A]{
    /** The index of the next value to return. */
    private var ix = 0

    /** Advance to the next value. */
    private def advance = while(ix < n && keys(ix) == null) ix += 1

    advance

    def hasNext = ix < n

    def next = { val k = keys(ix); ix += 1; advance; k }
  } // end of iterator

  /** Does this set contain x? */
  def contains(x: A): Boolean = { val i = find(x); keys(i) != null }

  /** Get the element of this that is equal (==) to x. 
    * Pre: such an element exists; and this operation is not concurrent with
    * any add operation. */
  def get(x: A): A = { val i = find(x); keys(i) }

  def size: Long = count

  def clear = {
    keys = new Array[A](initSize); count = 0; 
    n = initSize; mask = n-1; threshold = initSize * ThresholdRatio
  }
}

// =======================================================

/*An implementation of MyHashSet using a sharded hash table with
  * open addressing. 
  * @param shards the number of shards
  * @param initLength the initial length of each shard. */
class MyShardedHashSet[A : scala.reflect.ClassTag](
  shards: Int = LockFreeReadHashSet.powerOf2AboveNumThreads*16, 
  initLength: Int = 32)
    extends Sharding(shards) with MyHashSet[A]{
  /** Log (base 2) of the maximum width of rows in the arrays. */
  private val LogMaxWidth = 30

  /** Maximum width of rows in the arrays. */
  private val MaxWidth = 1<<LogMaxWidth

  // check initLength is a power of 2
  checkPow2(initLength)
  assert(initLength <= MaxWidth)

  /* We use a two-dimensional array, of size shards, with each row s
   * having width widths(s), to store states.  Inv: widths(s) is a
   * power of 2, widths(s) <= MaxWidth. */

  /** The number of entries in each shard. */
  private val widths: Array[Int] = Array.fill(shards)(initLength)

  /** Array holding the elements of the set. */
  private val elements = Array.fill(shards)(new Array[A](initLength))

  /** The hashes of the set. */
  private val hashes = Array.fill(shards)(new Array[Int](initLength))

  /** The current number of entries in each shard. */
  private val counts = new Array[Int](shards)

  /** Bit mask to produce a value in [0..width).  Inv: equals width-1. */
  private val widthMasks = Array.fill(shards)(initLength-1)

  /** Maximum load factor before resizing. */
  private val MaxLoad = 0.68

   /** Threshold at which resizing should be performed. */
  private val thresholds = Array.fill(shards)((initLength*MaxLoad).toInt)

  /** Locks: locks(s) protects shard(s). */
  private val locks = Array.fill(shards)(new AnyRef)

  /** The entry in shard sh = shardFor(h) in which a value with hash h
    * should be placed. */
  @inline private def entryFor(sh: Int, h: Int): Int = h & widthMasks(sh)

  /* An element with hash h is placed in shard sh = shardFor(h), in the
   * first empty (null) position in elements(sh) starting from
   * position entryFor(sh, h), wrapping round.  Its hash h is placed
   * in the corresponding position in hashes.  Note that we wrap
   * around in the same shard, rather than moving onto the next shard.  */

  /** The number of elements in this. */
  def size: Long = counts.map(_.toLong).sum

   /** Add x to the set.
    * @return true if x was not previously in the set. */
  def add(x: A): Boolean = {
    val h = hashOf(x); val sh = shardFor(h)
    locks(sh).synchronized{
      if(counts(sh) >= thresholds(sh)) resize(sh)
      // Find empty slot or slot containing x
      val i = find(sh, x, h)
      if(hashes(sh)(i) == h){ /* assert(elements(sh)(i) == x); */  false }
      else{
        // assert(hashes(sh)(i) == 0 && elements(sh)(i) == null)
        hashes(sh)(i) = h; elements(sh)(i) = x; counts(sh) += 1; true
      }
    }
  }

  /** Find the position at which element x with hash h is stored or should be
    * placed. */
  @inline private def find(sh: Int, x: A, h: Int): Int = {
    var i = entryFor(sh, h)
    // assert(i < widths(sh))
    while(hashes(sh)(i) != 0 && (hashes(sh)(i) != h || elements(sh)(i) != x))
      i = (i+1) & widthMasks(sh)
    i
  }

  /** Resize shard sh of the hash table. */
  @inline private def resize(sh: Int) = {
    // Increase width or height
    val oldWidth = widths(sh) // assert(oldWidth < MaxWidth, "too many elements")
    widths(sh) += oldWidth; widthMasks(sh) = widths(sh)-1
    thresholds(sh) += thresholds(sh)
    // Create new arrays
    val oldHashes = hashes(sh); hashes(sh) = new Array[Int](widths(sh))
    val oldElements = elements(sh); elements(sh) = new Array[A](widths(sh))
    // Copy elements
    var i = 0  //  index into oldHashes, oldElements
    while(i < oldWidth){
      val h = oldHashes(i)
      if(h != 0){ // add oldElements(i) to new table
        var i1 = entryFor(sh, h)
        while(hashes(sh)(i1) != 0) i1 = (i1+1) & widthMasks(sh)
        hashes(sh)(i1) = h
        // assert(elements(sh)(i1) == null)
        elements(sh)(i1) = oldElements(i)
      }
      i += 1
    }
  }

  /** Does this contain x?
    *  Pre: this operation is not concurrent to any add operation. */
  def contains(x: A): Boolean = ???

  /** An iterator over the elements of this.
    * Not thread safe. */
  def iterator: Iterator[A] = new Iterator[A]{
    /** Shard index and index of the next element. */
    private var sh = 0; private var i = 0

    advance

    /** Advance (sh, i) one step. */
    @inline private def advance1 = {
      i += 1; if(i == widths(sh)){ i = 0; sh += 1 }
    }

    /** Advance (sh, i) to the next element. */
    @inline private def advance =
      while(sh < shards && hashes(sh)(i) == 0) advance1

    /** Does the iterator have a next element? */
    def hasNext = sh < shards

    /** The next element of the iterator. */
    def next = { val result = elements(sh)(i); advance1; advance; result }
  } // end of iterator

  /** Get the element of this that is equal (==) to x. */
  def get(x: A): A = {
    val h = hashOf(x); val sh = shardFor(h)
    locks(sh).synchronized{
      val i = find(sh, x, h)
      // assert(elements(sh)(i) == x)
      elements(sh)(i)
    }
  }

  /** Get the element of this that is equal (==) to x, or add x if there
    * is no such. */
  def getOrAdd(x: A): A = {
    val h = hashOf(x); val sh = shardFor(h)
    locks(sh).synchronized{
      if(counts(sh) >= thresholds(sh)) resize(sh)
      val i = find(sh, x, h); val oldSt = elements(sh)(i)
      if(oldSt == null){
        hashes(sh)(i) = h; elements(sh)(i) = x; counts(sh) += 1; x
      }
      else{ /* assert(oldSt == x); */ oldSt }
    }
  }
}


// =======================================================

import java.util.concurrent.atomic.AtomicIntegerArray


/** An implementation of MyHashSet using a sharded hash table with open
  * addressing, and such that the add operation is lock-free if the element is
  * already in the set.
  * @param shards the number of shards
  * @param initLength the initial length of each shard. 
  * @param MaxLoad the maximum load factor before resizing.  */

class LockFreeReadHashSet[A : scala.reflect.ClassTag](
  shards: Int = LockFreeReadHashSet.DefaultShards,
  initLength: Int = 32,
  MaxLoad: Double = 0.666)
    extends Sharding(shards) with MyHashSet[A]{
  // println("LockFreeReadHashSet.shards = "+shards)

  // check initLength is a power of 2
  checkPow2(initLength)
  //assert(initLength <= MaxWidth)

  /** Maximum load factor before resizing. */
  //private val MaxLoad = 0.666 // 0.7 // 0.666

  /** We use a separate Shard obejct for each shard. */
  private class Shard(val n: Int){
    /** The hashes of the mapping. */
    val hashes = new java.util.concurrent.atomic.AtomicIntegerArray(n)

    /** The corresponding ServerState objects. */
    val values = new Array[A](n)

    /** Bit mask to produce a value in [0..n). */
    val mask = n-1

    /** Find the position at which element x with hash h is stored or
      * should be placed. */
    @inline def find(x: A, h: Int) : Int = {
      var i = h & mask
      while({ val h1 = hashes.get(i); h1 != 0 && (h1 != h || values(i) != x) })
        i = (i+1) & mask // (i+1)%n
      i
    }

    /* This represents the set { values(i) | hashes(i) != 0 }.
     * 
     * Each element is placed in the first empty (null) position
     * starting from its hash.  Its hash is placed in the
     * corresponding position in hashes.  Each entry is published when
     * its hash is written. */

    /** The current number of entries in this shard. */
    var count = 0

    /** Threshold at which resizing should be performed. */
    val threshold = (n*MaxLoad).toInt

    /** Must this be resized in order to add an entry? */
    @inline def mustResize = count >= threshold

    /** Does this shard contain x with hash h? */
    @inline def contains(x: A, h: Int): Boolean = {
      var i = h & mask; var h1 = hashes.get(i) // ; var count = 0
      while(h1 != 0 && (h1 != h || values(i) != x)){
        i = (i+1) & mask; h1 = hashes.get(i) // ; count += 1
      }
      h1 != 0
    }

  } // end of Shard class

  //private val Pad = 16 // padding doesn't seem to help

  @inline private def pad(sh: Int) = sh // Pad*sh

  /** The shards themselves. */
  private val theShards = new Array[Shard](shards)
  //  new java.util.concurrent.atomic.AtomicReferenceArray[Shard](pad(shards))

  /* Note (15/5/2019): If adds are not concurrent to any other operation, then
   * theShards doesn't need to use atomics, as follows. If an add reads a
   * stale value from theShards, but finds the value it is trying to add, it
   * correctly returns false (values are never deleted).  If an add fails to
   * find the value it is adding, it obtains the relevant lock, and re-reads
   * from theShards, necessarily getting the correct value.

   * With the introduction of newStyle && memoryless, adds can be concurrent
   * to contains operations.

   * If atomics are used, the profiler reports that 90%+ of the time of an add
   * is spent in getShard.  I don't understand this, but it doesn't seem
   * correct. */

  // IMPROVE: in-line following functions (as the compiler isn't taking the
  // hint).

  // 98% of the time for add is spent in the following function.
  @inline private def getShard(sh: Int) = 
    locks(sh).synchronized{ theShards(sh) }
    // theShards.get(pad(sh))

  @inline private def setShard(sh: Int, shard: Shard) = 
    // theShards.set(pad(sh), shard) 
    locks(sh).synchronized{ theShards(sh) = shard }

  /** Locks: locks(s) protects shard(s). */
  private val locks = Array.fill(shards)(new AnyRef)

  for(i <- 0 until shards) theShards(i) = new Shard(initLength)
  // setShard(i, new Shard(initLength))
  //  theShards.set(i, new Shard(initLength))

  /** The number of elements in this.  Not thread safe.*/
  def size = (0 until shards).map(i => getShard(i).count.toLong).sum

  /** Summary of sizes. */
  override def reportSizes: Array[Long] =
    (0 until shards).map(i => getShard(i).count.toLong).toArray

  /** Resize shard, returning new shard. */
  @inline private def resize(oldShard: Shard): Shard = { 
    val oldN = oldShard.n; val newShard = new Shard(oldN*2)
    newShard.count = oldShard.count
    //if(oldN > 500000) print("LFRHS resize to "+oldN*2)
    val mask = newShard.mask; var j = 0 // index into old arrays
    while(j < oldN){
      val h = oldShard.hashes.get(j)
      if(h != 0){ // add oldShard._(j) entries to new table
        var i = h & mask
        while(newShard.hashes.get(i) != 0) i = (i+1) & mask 
        newShard.values(i) = oldShard.values(j)
        newShard.hashes.set(i, h)
      }
      j += 1
    }
    //if(oldN > 500000) print("done.")
    newShard
  }

  /** Add x to the set.  
    * @return true if x was not previously in the set. */
  @inline def add(x: A): Boolean = {
    val h = hashOf(x); val sh = shardFor(h)
    var shard = getShard(sh) 
    var hashes = shard.hashes; val mask = shard.mask; var values = shard.values
    var i = h & mask; var h1 = hashes.get(i) // ; var count = 0 
    while(h1 != 0 && (h1 != h || values(i) != x)){
      i = (i+1) & mask; h1 = hashes.get(i) // ; count += 1
    }
    // if(count >= 150) print("LFRHS.add "+count+" "+sh+" "+(h&mask)+"; ")
    if(h1 == 0) locks(sh).synchronized{
      // Try to write new value.
      // Check state hasn't changed
      if(getShard(sh) != shard || hashes.get(i) != 0) add(x) // retry
      else{
        // Resize if necessary
        if(shard.mustResize){
          shard = resize(shard); setShard(sh, shard) // publish new shard
          i = shard.find(x, h); hashes = shard.hashes; values = shard.values
        }
        // Store in position i
        // assert(hashes.get(i) == 0 && shard.values(i) == null)
        values(i) = x; hashes.set(i, h) // publish update
        shard.count += 1; true
      }
    } // end of synchronized block
    else{ /* assert(h1 == h && shard.values(i) == x); */ false }
  }

  /** Does this contain x?   */
  def contains(x: A): Boolean = {
    val h = hashOf(x); getShard(shardFor(h)).contains(x, h)
    // val sh = shardFor(h)
    // var shard = getShard(sh); shard.contains(x, h) 
    // var hashes = shard.hashes; val mask = shard.mask; var values = shard.values
    // var i = h & mask; var h1 = hashes.get(i) // ; var count = 0 
    // while(h1 != 0 && (h1 != h || values(i) != x)){
    //   i = (i+1) & mask; h1 = hashes.get(i) // ; count += 1
    // }
    // h1 != 0
  }

  /** An iterator over the elements of this.
    * Not thread safe. */
  def iterator: Iterator[A] =  new Iterator[A]{
    /** Shard index, shard, and index of the next element. */
    private var sh = 0; private var shard = getShard(sh); private var i = 0

    advance

    /** Advance (sh, i) one step. */
    @inline private def advance1 = {
      i += 1;
      if(i == shard.n){
        i = 0; sh += 1; if(sh < shards) shard = getShard(sh)
      }
    }

    /** Advance (sh, i) to the next element. */
    @inline private def advance =
      while(sh < shards && shard.hashes.get(i) == 0) advance1

    /** Does the iterator have a next element? */
    def hasNext = sh < shards

    /** The next element of the iterator. */
    def next = { val result = shard.values(i); advance1; advance; result }
  } // end of iterator

  /** Get the element of this that is equal (==) to x. */
  def get(x: A): A =  {
    val h = hashOf(x); val sh = shardFor(h)
    val shard = getShard(sh) // volatile read; subscribe
    val i = shard.find(x, h)
    val y = shard.values(i)
    // assert(y == x)
    y
  }

  /** Get the element of this that is equal (==) to x, or add x if there
    * is no such. */
  def getOrAdd(x: A): A = ???
}

// =======================================================

object LockFreeReadHashSet{

  /** numThreads rounded up to next power of 2. 
    * This is used in deciding the size of some sharded hash tables.  */
  val powerOf2AboveNumThreads = {
    var pow = 1; var nt = numThreads
    while(nt > 1){ pow *= 2; nt = (nt-1)/2+1 }
    pow
  }
  // IMPROVE: use powerOfTwoAtLeast

  val DefaultShards = powerOf2AboveNumThreads*16 
}
