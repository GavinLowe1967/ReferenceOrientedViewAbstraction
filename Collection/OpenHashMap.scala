package ViewAbstraction.collection

import ViewAbstraction.{hashOf,checkPow2,numThreads}

class OpenHashMap[A: scala.reflect.ClassTag, B: scala.reflect.ClassTag](
  initSize: Int = 16, ThresholdRatio: Float = 0.5F){

  checkPow2(initSize)

  /** The number of keys. */
  private var count = 0L

 /** The number of slots in the hash table. */
  private var n = initSize

  /** A bitmask to produce a value in [0..n). */
  private var mask = n-1

  /** The threshold at which the next resizing will happen. */
  private var threshold = initSize * ThresholdRatio

  /** The array holding the keys. */
  private var keys = new Array[A](initSize)

  /** The array holding the values. */
  private var values = new Array[B](initSize)

  /** The array holding the hashes. 
    * Invariant, if keys(i) != null then hashes(i) = hashOf(keys(i));
    * if keys(i) == null then hashes(i) == 0. */
  private var hashes = new Array[Int](initSize)

  /** Find the index in the arrays corresponding to k with hashCode h. */
  @inline private def find(a: A, h: Int): Int = {
    var i = h & mask
    while(hashes(i) != 0 && (hashes(i) != h || keys(i) != a))
      i = (i+1)&mask
    i
  }  

  /** Optionally get the value associated with a. */
  def get(a: A): Option[B] = {
    val h = hashOf(a); val i = find(a, h)
    if(hashes(i) == 0){ assert(keys(i) == null); None }
    else{ assert(hashes(i) == h && keys(i) == a); Some(values(i)) }
  }

  /** Add the mapping a -> b. */
  def add(a: A, b: B) = {
    require(a != null.asInstanceOf[A])
    if(count >= threshold) resize()
    val h = hashOf(a); val i = find(a, h)
    if(hashes(i) == 0){ 
      assert(keys(i) == null)
      hashes(i) = h; keys(i) = a; values(i) = b; count += 1
    }
    else{ 
      assert(hashes(i) == h && keys(i) == a); values(i) = b 
    }
  }

  /** Resize the hash table. */
  @inline private def resize() = {
    val oldKeys = keys; val oldHashes = hashes; val oldValues = values
    val oldN = n; n += n; threshold = n * ThresholdRatio; mask = n-1
    keys = new Array[A](n); hashes = new Array[Int](n); values = new Array[B](n)
    var i = 0
    while(i < oldN){
      val k = oldKeys(i)
      if(k != null){ // copy across
        val h = oldHashes(i); val j = find(k,h) 
        keys(j) = k; hashes(j) = h; values(j) = oldValues(i)
      }
      i += 1
    }
  }


}
