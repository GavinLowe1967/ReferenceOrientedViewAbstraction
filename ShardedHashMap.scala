package ViewAbstraction


/** An implementation of MyHashMap using a sharded hash table with
  * open addressing. 
  * @param shards the number of shards
  * @param initLength the initial length of each shard. */
class ShardedHashMap[A: scala.reflect.ClassTag, B: scala.reflect.ClassTag](
  shards: Int = 128, initLength: Int = 32){

  checkPow2(initLength)

  /** Value representing an empty slot in hashes. */
  private val Empty = 0    // = 000...0 binary

  /** Value representing a deleted slot in hashes. */
  private val Deleted = -1 // = 111...1 binary

  /* If the hashCode of a key is either Empty or Deleted, we replace it by
   * EmptyProxy or DeletedProxy, respectively (flipping most significant
   * bit). */
  private val EmptyProxy = Empty ^ Int.MinValue     // = 1000...0 binary
  private val DeletedProxy = Deleted ^ Int.MinValue // = 0111...1 binary

  /** A hash for a; guaranteed not to be Empty or Deleted. */
  private def hashOf(a: A): Int = {
    val h = a.hashCode
    if(h == Empty) EmptyProxy else if(h == Deleted) DeletedProxy else h 
  }

  /** Does the hash value h represent a used slot (neither Empty nor
    * Deleted)? */
  @inline private def filled(h: Int) = h != Empty && h != Deleted

  /* We use a two-dimensional array, of size shards, with each row s
   * having width widths(s), to store states.  Inv: widths(s) is a
   * power of 2, widths(s) <= MaxWidth. */

  /** The number of entries in each shard. */
  private var widths: Array[Int] = Array.fill(shards)(initLength)

  /** Array holding the keys of the map. */
  private val keys = Array.fill(shards)(new Array[A](initLength))

  /** Array holding the elements of the set. */
  private var elements = Array.fill(shards)(new Array[B](initLength))

  /** The hashes of the set, with Empty representing an empty slot, and Deleted
    * representing an entry that has been deleted.  Initially all Empty (0). */
  private var hashes = Array.fill(shards)(new Array[Int](initLength))

  /** The current number of proper entries in each shard. */
  private var counts = new Array[Int](shards)

  /** The current number of used slots in each shard (including Deleted
    * values). */
  private val usedSlots = new Array[Int](shards)

  /** Bit mask to produce a value in [0..width).  Inv: for each sh,
    * widthMasks(sh) = widths(sh)-1. */
  private var widthMasks = Array.fill(shards)(initLength-1)

  /** Maximum load factor before resizing. */
  private val MaxLoad = 0.5

   /** Threshold at which resizing should be performed. */
  private val thresholds = Array.fill(shards)((initLength*MaxLoad).toInt)

  /** Locks: locks(s) protects shard(s). */
  private val locks = Array.fill(shards)(new AnyRef)

  /** Bit shift to produce a value in [0..shards).  */
  private var shardShift = {
    var s = shards; var ss = 0 // Inv shards = s * 2^ss
    while(s > 1){
      assert((s&1) == 0); s = s >>> 1; ss += 1
    }
    32-ss
  }
  // println("shardShift = "+shardShift)

  /** The shard to use for a value with hash h; the most significant
    * bits of h. */
  @inline private def shardFor(h: Int) = h >>> shardShift

  /** The entry in shard sh = shardFor(h) in which a value with hash h
    * should be placed. */
  @inline private def entryFor(sh: Int, h: Int): Int = h & widthMasks(sh)

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
  @noinline private def find(sh: Int, x: A, h: Int): Int = {
    var i = entryFor(sh, h)
    assert(i < widths(sh))
    while(hashes(sh)(i) != 0 && (hashes(sh)(i) != h || keys(sh)(i) != x))
      i = (i+1) & widthMasks(sh)
    i
  }

  /** Get the value associated with a, if one exits; otherwise update it
    * to the value of b. */
  def getOrElseUpdate(a: A, b: => B): B = {
    val h = hashOf(a); val sh = shardFor(h)
    locks(sh).synchronized{
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

  /** Get the value associated with a; or default if there is no such value. */
  def getOrElse(a: A, default: => B) = {
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
      // Find empty slot or slot containing x
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

  def += (pair: (A, B)) = add(pair._1, pair._2)

  /** Resize shard sh of the hash table. */
  @inline private def resize(sh: Int) = {
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

  /** Remove the value associated with a, optionally returning the value
    * associated with it. */
  def remove(a: A): Option[B] = {
    val h = hashOf(a); val sh = shardFor(h)
    locks(sh).synchronized{
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
