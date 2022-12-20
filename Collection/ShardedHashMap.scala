package ViewAbstraction.collection

// import ViewAbstraction.{checkPow2}

import scala.reflect.ClassTag

/** A base class for sharded hash maps with open addressing.
  * 
  * Extended by ShardedHashMap and ShardedLockableMap
  * @param shards the number of shards
  * @param initLength the initial length of each shard. */
abstract class ShardedHashMap0[A, B] // [A: ClassTag, B: ClassTag](
  (shards: Int, initLength: Int)
  (implicit tagA: ClassTag[A],  tagB: ClassTag[B]){

  ViewAbstraction.checkPow2(initLength)

  import DeletableMap._    // Empty, Deleted, hashOf, filled

  /* We use a two-dimensional array, of size shards, with each row s
   * having width widths(s), to store states.  Inv: widths(s) is a
   * power of 2, widths(s) <= MaxWidth. */

  /** The number of entries in each shard. */
  protected var widths: Array[Int] = Array.fill(shards)(initLength)

  /** Array holding the keys of the map. */
  protected val keys = Array.fill(shards)(new Array[A](initLength))

  /** Array holding the elements of the set. */
  protected var elements = Array.fill(shards)(new Array[B](initLength))

  /** The hashes of the set, with Empty representing an empty slot, and Deleted
    * representing an entry that has been deleted.  Initially all Empty (0). */
  protected var hashes = Array.fill(shards)(new Array[Int](initLength))

  /** The current number of proper entries in each shard. */
  protected var counts = new Array[Int](shards)

  /** The current number of used slots in each shard (including Deleted
    * values). */
  protected val usedSlots = new Array[Int](shards)

  /** Bit mask to produce a value in [0..width).  Inv: for each sh,
    * widthMasks(sh) = widths(sh)-1. */
  protected var widthMasks = Array.fill(shards)(initLength-1)

  /** Maximum load factor before resizing. */
  protected val MaxLoad = 0.5

   /** Threshold at which resizing should be performed. */
  protected val thresholds = Array.fill(shards)((initLength*MaxLoad).toInt)

  /** Locks: locks(s) protects shard(s). */
  protected val locks = Array.fill(shards)(new AnyRef)

  /** Bit shift to produce a value in [0..shards).  */
  protected var shardShift = {
    var s = shards; var ss = 0 // Inv shards = s * 2^ss
    while(s > 1){
      assert((s&1) == 0); s = s >>> 1; ss += 1
    }
    32-ss
  }
  // println("shardShift = "+shardShift)

  /** The shard to use for a value with hash h; the most significant
    * bits of h. */
  @inline protected def shardFor(h: Int) = h >>> shardShift

  /** The entry in shard sh = shardFor(h) in which a value with hash h
    * should be placed. */
  @inline protected def entryFor(sh: Int, h: Int): Int = h & widthMasks(sh)

  /* An element with hash h is placed in shard sh = shardFor(h), in the
   * first empty (null) position in keys(sh) and elements(sh), starting
   * from position entryFor(sh, h), wrapping round.  Its hash h is
   * placed in the corresponding position in hashes.  Note that we
   * wrap around in the same shard, rather than moving onto the next
   * shard.  */

  /** The number of elements in this. */
  def size: Int = counts.sum

  /** Find the position at which element x with hash h is stored or should be
    * placed. */
  @noinline protected def find(sh: Int, x: A, h: Int): Int = {
    var i = entryFor(sh, h)
    assert(i < widths(sh))
    while(hashes(sh)(i) != 0 && (hashes(sh)(i) != h || keys(sh)(i) != x))
      i = (i+1) & widthMasks(sh)
    i
  }

  /** Get the value associated with a, with hash h, in shard sh, if one exits;
    * otherwise update it to the value of b. */
  @inline protected def getOrElseUpdate(a: A, b: => B, h: Int, sh: Int)
      : B = locks(sh).synchronized{
    if(usedSlots(sh) >= thresholds(sh)) resize(sh)
    // Find empty slot or slot containing x
    val i = find(sh, a, h)
    if(hashes(sh)(i) == h){ assert(keys(sh)(i) == a); elements(sh)(i) }
    else{
      // println("Adding "+a+" -> "+b)
      assert(hashes(sh)(i) == 0 && keys(sh)(i) == null &&
        elements(sh)(i) == null)
      hashes(sh)(i) = h; keys(sh)(i) = a; val myB = b; elements(sh)(i) = myB
      counts(sh) += 1; usedSlots(sh) += 1; myB
    }
  }

  /** Resize shard sh of the hash table. */
  @inline protected def resize(sh: Int) = {
    // Increase width of shard sh
    val oldWidth = widths(sh); val newWidth = 2*oldWidth
    widths(sh) = newWidth; val mask = newWidth-1; widthMasks(sh) = mask
    thresholds(sh) += thresholds(sh); usedSlots(sh) = counts(sh)
    // println("Resizing hash map "+sh+" to"+newWidth)
    // Create new arrays
    val oldHashes = hashes(sh); hashes(sh) = new Array[Int](newWidth)
    val oldElements = elements(sh); elements(sh) = new Array[B](newWidth)
    val oldKeys = keys(sh); keys(sh) = new Array[A](newWidth)
    // Copy elements
    var i = 0  //  index into oldHashes, oldElements
    var theCount = 0
    while(i < oldWidth){
      val h = oldHashes(i)
      if(filled(h)){ // add oldElements(i) to new table
        var i1 = entryFor(sh, h)
        // Note: we don't copy Deleted values, so enough to compare with Empty
        while(hashes(sh)(i1) != Empty) i1 = (i1+1) & mask
        hashes(sh)(i1) = h; theCount += 1
        assert(elements(sh)(i1) == null && keys(sh)(i1) == null)
        elements(sh)(i1) = oldElements(i); keys(sh)(i1) = oldKeys(i)
      }
      i += 1
    } // end of while loop
    assert(theCount == counts(sh))
  }

  /** Update the mapping so a -> b, where a has hash h and is in shard sh.  Pre:
    * a is already in the domain.  Can be used while there is an iteration
    * happening. */
  @inline protected def replace(a: A, b: B, h: Int, sh: Int)
      : Unit = locks(sh).synchronized{
    // Find slot containing a
    val i = find(sh, a, h)
    assert(hashes(sh)(i) == h && keys(sh)(i) == a)
    elements(sh)(i) = b
  }

  /** Remove the value associated with a, where a has hash h and is in shard sh,
    * optionally returning the value associated with it. */
  @inline protected def remove(a: A, h: Int, sh: Int)
      : Option[B] = locks(sh).synchronized{
    val i = find(sh, a, h)
    if(hashes(sh)(i) == h){
      assert(keys(sh)(i) == a)
      // Note: clearing key and elements might allow garbage collection
      hashes(sh)(i) = Deleted; keys(sh)(i) = null.asInstanceOf[A]
      val b = elements(sh)(i); elements(sh)(i) = null.asInstanceOf[B]
      counts(sh) -= 1; Some(b)
    }
    else{ assert(hashes(sh)(i) == 0); None }
  }

  // ========= Iterators

  /** An iterator over the (key, value) pairs in shard sh. */
  private def shardIterator(sh: Int) = new Iterator[(A,B)]{
    /** Current index in the shard. */
    private var ix = 0

    private val theWidth = widths(sh)

    /** Advance to the next element. */
    private def advance(): Unit = 
      while(ix < theWidth && !filled(hashes(sh)(ix))) ix += 1

    advance()

    def hasNext = ix < theWidth

    def next() = {
      assert(elements(sh)(ix) != null, "hash = "+hashes(sh)(ix))
      val res = (keys(sh)(ix), elements(sh)(ix)); ix += 1; advance(); res 
    }
  } // end of shardIterator

  /** Objects that produce iterators over the different shards.  This is
    * thread-safe, but each iterator it produces is not. */
  class ShardIteratorProducer extends ShardedHashMap.ShardIteratorProducerT[A,B]{
    private var sh = 0

    /** Get the next iterator, or null if we're done. */
    def get: Iterator[(A,B)] = synchronized{
      if(sh < shards){ val iter = shardIterator(sh); sh += 1; iter }
      else null
    }
  } // end of ShardIteratorProducer

  /** An object that produces Iterator[(A,B)]s, each over the next shard. */
  def shardIteratorProducer = new ShardIteratorProducer

}

// ==================================================================

/** A sharded hash map with open addressing.
  * @param shards the number of shards
  * @param initLength the initial length of each shard. */
class ShardedHashMap[A, B](shards: Int = 128, initLength: Int = 32)
  (implicit tagA: ClassTag[A], tagB: ClassTag[B])
    extends ShardedHashMap0(shards, initLength)(tagA, tagB){

  import DeletableMap._    // Empty, Deleted, hashOf, filled

  /** Get the value associated with a, if one exits; otherwise update it
    * to the value of b. */
  def getOrElseUpdate(a: A, b: => B): B = {
    val h = hashOf(a); getOrElseUpdate(a, b, h, shardFor(h))
  }

  /** Optionally get the value associated with a. */
  def get(a: A): Option[B] = {
    val h = hashOf(a); val sh = shardFor(h)
    locks(sh).synchronized{
      val i = find(sh, a, h)
      if(hashes(sh)(i) == h){ assert(keys(sh)(i) == a); Some(elements(sh)(i)) }
      else{ assert(hashes(sh)(i) == 0); None }
    }
  }

  /** Get the value associated with a.  Pre: a is in the mapping. */
  def apply(a: A): B = {
    val h = hashOf(a); val sh = shardFor(h)
    locks(sh).synchronized{
      val i = find(sh, a, h)
      assert(hashes(sh)(i) == h && keys(sh)(i) == a, s"Key not found: $a")
      elements(sh)(i)
    }
  }

  def contains(a: A): Boolean = {
    val h = hashOf(a); val sh = shardFor(h)
    // The hash in the position corresponding to h
    val h1 =  locks(sh).synchronized{
      val i = find(sh, a, h); hashes(sh)(i)
    }
    if(filled(h1)){ assert(h1 == h); true }
    else false
  }

  /** Get the value associated with a; or default if there is no such value. */
  def getOrElse(a: A, default: => B): B = {
    val h = hashOf(a); val sh = shardFor(h)
    locks(sh).synchronized{
      val i = find(sh, a, h)
      if(hashes(sh)(i) == h){ assert(keys(sh)(i) == a); elements(sh)(i) }
      else{ assert(hashes(sh)(i) == 0); default }
    }
  }

  /** Add the mapping a -> b to the map. */
  def add(a: A, b: B) = {
    val h = hashOf(a); val sh = shardFor(h)
    locks(sh).synchronized{
      if(usedSlots(sh) >= thresholds(sh)) resize(sh)
      // Find empty slot or slot containing a
      val i = find(sh, a, h)
      if(hashes(sh)(i) == h){ assert(keys(sh)(i) == a); elements(sh)(i) = b }
      else{
        // println("Adding "+a+" -> "+b)
        assert(hashes(sh)(i) == 0 && keys(sh)(i) == null && 
          elements(sh)(i) == null)
        hashes(sh)(i) = h; keys(sh)(i) = a; elements(sh)(i) = b
        counts(sh) += 1; usedSlots(sh) += 1
      }
    }
  }

  /** Update the mapping so a -> b.  Pre: a is already in the domain.  Can be
    * used while there is an iteration happening. */
  def replace(a: A, b: B): Unit = {
    val h = hashOf(a); val sh = shardFor(h); replace(a, b, h, sh)
  }

  /** Add pair._1 -> pair._2 to the map. */
  def += (pair: (A, B)) = add(pair._1, pair._2)

  /** If a -> expB is in the map, then update so a -> newB.  Return true if
    * successful. */
  def compareAndSet(a: A, expB: B, newB: => B): Boolean = {
    val h = hashOf(a); val sh = shardFor(h)
    locks(sh).synchronized{
      if(usedSlots(sh) >= thresholds(sh)) resize(sh)
      // Find empty slot or slot containing x
      val i = find(sh, a, h)
      if(hashes(sh)(i) == h && elements(sh)(i) == expB){
        elements(sh)(i) = newB; true 
      } 
      else false
    }
  }

  /** Remove the value associated with a, optionally returning the value
    * associated with it. */
  def remove(a: A): Option[B] = {
    val h = hashOf(a); val sh = shardFor(h); remove(a, h, sh)
  }

  /** If a -> b is in the map then remove it.  Return true if successful. */
  def removeIfEquals(a: A, b: B): Boolean = {
    val h = hashOf(a); val sh = shardFor(h)
    locks(sh).synchronized{
      val i = find(sh, a, h)
      if(hashes(sh)(i) == h && elements(sh)(i) == b){
        assert(keys(sh)(i) == a)
        // Note: clearing key and elements might allow garbage collection
        hashes(sh)(i) = Deleted; keys(sh)(i) = null.asInstanceOf[A]
        elements(sh)(i) = null.asInstanceOf[B]; counts(sh) -= 1; true
      }
      else{ assert(hashes(sh)(i) == 0 || keys(sh)(i) == a); false }
    }
  }

  /** An iterator over the range of this map. */
  def valuesIterator = new Iterator[B]{
    /** Current shard. */
    private var sh = 0

    /** Current index in that shard. */
    private var ix = 0

    /* We maintain the invariant that sh and ix point to the next element to be
     * returned. */

    /** Advance to the next element. */
    private def advance(): Unit = {
      // Advance within this shard
      while(ix < widths(sh) && !filled(hashes(sh)(ix))) ix += 1
      // Maybe move to next shard
      if(ix == widths(sh)){ sh += 1; ix = 0; if(sh < shards) advance() }
    }

    advance()

    def hasNext = sh < shards 

    def next() = { val res = elements(sh)(ix); ix += 1; advance(); res }
  } // end of Iterator

  /** An iterator over the (key, value) pairs in this map. */
  def iterator = new Iterator[(A,B)]{
    /** Current shard. */
    private var sh = 0

    /** Current index in that shard. */
    private var ix = 0

    /* We maintain the invariant that sh and ix point to the next element to be
     * returned. */

    /** Advance to the next element. */
    private def advance(): Unit = {
      // Advance within this shard
      while(ix < widths(sh) && !filled(hashes(sh)(ix))) ix += 1
      // Maybe move to next shard
      if(ix == widths(sh)){ sh += 1; ix = 0; if(sh < shards) advance() }
    }

    advance()

    def hasNext = sh < shards 

    def next() = { 
      val res = (keys(sh)(ix), elements(sh)(ix)); ix += 1; advance(); res 
    }
  } // end of iterator
}


// ==================================================================

object ShardedHashMap{
  /** Objects that produce iterators over the different shards. */
  trait ShardIteratorProducerT[A,B]{
    def get: Iterator[(A,B)]

    /** Cooperate on applying `process` to each pair in the underlying 
      * mapping. */ 
    def foreach(process: (A,B) => Unit) = {
      var shardIterator = get
      while(shardIterator != null){
        for((a,b) <- shardIterator) process(a,b)
        shardIterator = get
      }
    }
  }
}
