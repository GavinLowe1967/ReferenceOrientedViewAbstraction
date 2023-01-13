package ViewAbstraction.collection

/** A mapping K => D, implemented using a hash map. 
  * The implementation assumes that keys cannot be null.
  * @param initSize the initial size of the hash table.
  * @param init code to initialise a new data value. */
class BasicHashMap[K: scala.reflect.ClassTag, D: scala.reflect.ClassTag]
    (initSize: Int = 16, init: => D){
  checkPow2(initSize)

  /** The number of keys. */
  private var count = 0

 /** The number of slots in the hash table. */
  private var n = initSize

  /** A bitmask to produce a value in [0..n). */
  private var mask = n-1

  /** The threshold ratio at which resizing happens. */
  private val ThresholdRatio = 0.7

  /** The threshold at which the next resizing will happen. */
  private var threshold = initSize * ThresholdRatio

  /** The array holding the keys. */
  private var keys = new Array[K](initSize)

  /** The array holding the corresponding D values. */
  private var data = new Array[D](initSize)

  /** Find the index in the arrays corresponding to k. */
  private def find(k: K): Int = {
    var i = k.hashCode & mask
    while(keys(i) != k && keys(i) != null) i = (i+1)&mask
    i
  }

  /** Get the data associated with k, initialising it if necessary. */
  def getOrInit(k: K): D = {
    val i = find(k)
    if(keys(i) == null){
      if(count >= threshold){ resize(); return getOrInit(k) }
      keys(i) = k; data(i) = init; count += 1
    }
    data(i)
  }

  /** Add the mapping k -> d. */
  def add(k: K, d: D): Unit = {
    val i = find(k)
    if(keys(i) == null){
      if(count >= threshold){ resize(); return add(k,d) }
      keys(i) = k; count += 1
    }
    data(i) = d
  }

  /** Get the value associated with k, or null if there is no such. */
  def get(k: K): D = { val i = find(k); data(i) }

  /** Optionally get the value associated with k. */
  def optGet(k: K): Option[D] = { 
    val i = find(k); if(keys(i) != null) Some(data(i)) else None 
  }

  /** Resize the hash table. */
  private def resize(): Unit = {
    // println("resizing")
    val oldKeys = keys; val oldData = data; val oldN = n
    n += n; threshold = n * ThresholdRatio; mask = n-1
    keys = new Array[K](n); data = new Array[D](n); var i = 0
    while(i < oldN){
      val k = oldKeys(i)
      if(k != null){ // copy across
        val j = find(k); keys(j) = k; data(j) = oldData(i)
      }
      i += 1
    }
  }

  /** An iterator over the D values. */
  def iterator = new Iterator[D]{
    /** The index of the next value to return. */
    private var ix = 0

    /** Advance to the next value. */
    private def advance = while(ix < n && keys(ix) == null) ix += 1

    advance

    def hasNext = ix < n

    def next() = { val d = data(ix); ix += 1; advance; d }
  } // end of iterator
} // end of BasicHashMap
