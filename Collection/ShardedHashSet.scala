package ViewAbstraction.collection

import ViewAbstraction.checkPow2
// import collection.{Sharding,LockFreeReadHashSet}

/*An implementation of MyHashSet using a sharded hash table with
  * open addressing. 
  * @param shards the number of shards
  * @param initLength the initial length of each shard. */
class ShardedHashSet[A : scala.reflect.ClassTag](
  shards: Int = LockFreeReadHashSet.powerOf2AboveNumThreads*16, 
  initLength: Int = 32)
    extends Sharding(shards) with MyHashSet[A]{

  import ShardedHashSet.{Empty,Deleted,EmptyProxy,DeletedProxy,MaxWidth}

  // check initLength is a power of 2 
  checkPow2(initLength)
  assert(initLength <= MaxWidth)

  /* In hashes, Empty (= 0) represents an empty slot, and Deleted represents a
   * deleted slot.  If the hashCode of a key is either Empty or Deleted, we
   * replace it by EmptyProxy or DeletedProxy, respectively. */

  /** A hash for a; guaranteed not to be Empty or Deleted. */
  private def hashOf(a: A): Int = {
    val h = scala.util.hashing.byteswap32(a.hashCode)
    if(h == Empty) EmptyProxy else if(h == Deleted) DeletedProxy else h 
  }

  /** Does the hash value h represent a used slot (neither Empty nor
    * Deleted)? */
  @inline private def filled(h: Int) = h != Empty && h != Deleted

  /** Does the hash value h represent an unused slot (either Empty or
    * Deleted)? */
  @inline private def unfilled(h: Int) = h == Empty || h == Deleted

  /* We use a two-dimensional array, of size shards, with each row s
   * having width widths(s), to store states.  Inv: widths(s) is a
   * power of 2, widths(s) <= MaxWidth. */

  /** The number of spaces in each shard. */
  private val widths: Array[Int] = Array.fill(shards)(initLength)

  /** Array holding the elements of the set. */
  private val elements = Array.fill(shards)(new Array[A](initLength))

  /** The hashes of the set. */
  private val hashes = Array.fill(shards)(new Array[Int](initLength))

  /** The current number of entries in each shard (excluding Deleted values). */
  private val counts = new Array[Int](shards)

  /** The current number of used slots in each shard (including Deleted
    * values). */
  private val usedSlots = new Array[Int](shards)

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

  /* An element with hash h is placed in shard sh = shardFor(h), in the first
   * empty (null) position in elements(sh) starting from position entryFor(sh,
   * h), wrapping round.  Its hash h is placed in the corresponding position
   * in hashes.  For slots where a value has been deleted, the hash is
   * Deleted, and the element is null.  Note that we wrap around in the same
   * shard, rather than moving onto the next shard.  */

  /** The number of elements in this. */
  def size: Long = counts.map(_.toLong).sum

  /** Find the position at which element x with hash h is stored, or the first
    * Empty slot, where h should be placed.  Note: we skip over Deleted
    * items. */
  @inline private def find(sh: Int, x: A, h: Int): Int = {
    var i = entryFor(sh, h)
    // assert(i < widths(sh))
    while(hashes(sh)(i) != Empty && (hashes(sh)(i) != h || elements(sh)(i) != x))
      i = (i+1) & widthMasks(sh)
    i
  }

  /** Add x to the set.
    * @return true if x was not previously in the set. */
  def add(x: A): Boolean = {
    val h = hashOf(x); val sh = shardFor(h)
    locks(sh).synchronized{
      if(usedSlots(sh) >= thresholds(sh)) resize(sh)
      // Find empty slot or slot containing x
      val i = find(sh, x, h)
      if(hashes(sh)(i) == h){ /*assert(elements(sh)(i) == x);*/ false }
      else{
        // assert(hashes(sh)(i) == Empty && elements(sh)(i) == null)
        hashes(sh)(i) = h; elements(sh)(i) = x; 
        counts(sh) += 1; usedSlots(sh) += 1; true
      }
    }
  }

  /** Resize shard sh of the hash table. */
  @inline private def resize(sh: Int) = {
    // Increase width or height
    val oldWidth = widths(sh) // assert(oldWidth < MaxWidth, "too many elements")
// IMPROVE: if usedSlots(sh) is small, keep oldWidth? 
    widths(sh) += oldWidth; widthMasks(sh) = widths(sh)-1
    thresholds(sh) += thresholds(sh)
    // Create new arrays
    val oldHashes = hashes(sh); hashes(sh) = new Array[Int](widths(sh))
    val oldElements = elements(sh); elements(sh) = new Array[A](widths(sh))
    // Copy elements
    var i = 0  //  index into oldHashes, oldElements
    while(i < oldWidth){
      val h = oldHashes(i)
      if(filled(h)){ // add oldElements(i) to new table
        var i1 = entryFor(sh, h)
        while(hashes(sh)(i1) != Empty) i1 = (i1+1) & widthMasks(sh)
        hashes(sh)(i1) = h
        // assert(elements(sh)(i1) == null)
        elements(sh)(i1) = oldElements(i)
      }
      i += 1
    }
    usedSlots(sh) = counts(sh)
  }

  /** Does this contain x? */
  def contains(x: A): Boolean = {
    val h = hashOf(x); val sh = shardFor(h)
    locks(sh).synchronized{ shardContains(sh, x, h) }
    //   val i = find(sh, x, h)
    //   elements(sh)(i) == x // IMPROVE: replace with test of hash
    // }
  }

  /** Does shard sh contain x with hash h? */
  @inline private def shardContains(sh: Int, x: A, h: Int): Boolean = {
    val i = find(sh, x, h); hashes(sh)(i) == h
    // elements(sh)(i) == x // IMPROVE: replace with test of hash
  }

  /** Does this contain x?  Performed in a lock-free way.  Should not be called
    * concurrently to any add operation, but may be concurrent with a
    * remove.  */
  def lockFreeContains(x: A): Boolean = { 
    val h = hashOf(x); val sh = shardFor(h); shardContains(sh, x, h) 
  }

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
      while(sh < shards && unfilled(hashes(sh)(i))) advance1

    /** Does the iterator have a next element? */
    def hasNext = sh < shards

    /** The next element of the iterator. */
    def next() = { val result = elements(sh)(i); advance1; advance; result }
  } // end of iterator


  /** An iterator over shard sh.  Not thread-safe. */
  private def shardIterator(sh: Int) = new Iterator[A]{
    require(sh < shards)
    // Index into arrays
    private var i = 0
    // Size of this shard
    private val thisWidth = widths(sh)

    advance()

    @inline private def advance() = 
      while(i < thisWidth && unfilled(hashes(sh)(i))) i += 1

    def hasNext = i < thisWidth

    def next() = { val res = elements(sh)(i); i += 1; advance(); res }
  }

  /** Objects that produce iterators over the different shards.  This is
    * thread-safe, but each iterator it produces is not. */
  class ShardIteratorProducer extends ShardedHashSet.ShardIteratorProducerT[A]{
    private var sh = 0

    /** Get the next iterator, or null if we're done. */
    def get: Iterator[A] = synchronized{
      if(sh < shards){ val iter = shardIterator(sh); sh += 1; iter }
      else null
    }
  } // end of ShardIteratorProducer

  /** An object that produces Iterator[A]s, each over the next shard. */
  def shardIteratorProducer = new ShardIteratorProducer

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
      if(usedSlots(sh) >= thresholds(sh)) resize(sh)
      val i = find(sh, x, h); val oldSt = elements(sh)(i)
      if(oldSt == null){
        assert(hashes(sh)(i) == Empty && elements(sh)(i) == null)
        hashes(sh)(i) = h; elements(sh)(i) = x; 
        counts(sh) += 1; usedSlots(sh) += 1; x
      }
      else{ assert(oldSt == x);  oldSt } // IMPROVE
    }
  }

  /** Remove x from the set.  Return true if successful. */
  def remove(x: A): Boolean = {
    val h = hashOf(x); val sh = shardFor(h)
    locks(sh).synchronized{
      val i = find(sh, x, h)
      if(hashes(sh)(i) == h){
        // assert(elements(sh)(i) == x); 
        hashes(sh)(i) = Deleted
        elements(sh)(i) = null.asInstanceOf[A]; counts(sh) -= 1; true
      }
      else{ assert(elements(sh)(i) == null.asInstanceOf[A]); false }
    }
  }
}

// ==================================================================

object ShardedHashSet{
  /** Log (base 2) of the maximum width of rows in the arrays. */
  private val LogMaxWidth = 30

  /** Maximum width of rows in the arrays. */
  private val MaxWidth = 1<<LogMaxWidth

  /** Value representing an empty slot in hashes. */
  private val Empty = 0    // = 000...0 binary

  /** Value representing a deleted slot in hashes. */
  private val Deleted = -1 // = 111...1 binary

  /* If the hashCode of a key is either Empty or Deleted, we replace it by
   * EmptyProxy or DeletedProxy, respectively (flipping most significant
   * bit). */
  private val EmptyProxy = Empty ^ Int.MinValue     // = 1000...0 binary
  private val DeletedProxy = Deleted ^ Int.MinValue // = 0111...1 binary


  /** Objects that produce iterators over the different shards. */
  trait ShardIteratorProducerT[A]{
    def get: Iterator[A]
  }
}
