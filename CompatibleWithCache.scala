package ViewAbstraction

import scala.collection.mutable.{HashMap}
import ViewAbstraction.BasicHashMap

/** A mapping used to cache the results of Checker.compatibleWith.  Abstractly
  * a mapping from CompatibleWithCache.Key to CompatibleWithCache.Cache. */
class CompatibleWithCache{
  import CompatibleWithCache.{Key,Cache}

  private val compatibleWithCache = new HashMap[Key, Cache]

  /** Get the Cache associated with Key. */
  def get(key: Key): Cache = synchronized{ 
    compatibleWithCache.getOrElseUpdate(key, new Cache) 
  }
}

// ==================================================================

/**Companion object for CompatibleWithCache. */
object CompatibleWithCache{
  /** The type of keys used in the cache. */
  type Key = (List[State], List[List[Identity]], List[List[Identity]])

  /** The type of the cache of the results for a particular Key. */
  type Cache = ResultCache // BasicHashMap[List[State], Boolean]
}

// ==================================================================

/** The results for a particular Key, abstractly a mapping from Array[State]
  * to Boolean. */
class ResultCache(initSize: Int = 16){
  type States = Array[State]

  checkPow2(initSize)

  /** The number of keys. */
  private var count = 0

  /** The number of slots in the hash table. */
  private var n = initSize

  /** A bitmask to produce a value in [0..n). */
  private var mask = n-1

  /** The threshold ratio at which resizing happens. */
  private val ThresholdRatio = 0.5

  /** The threshold at which the next resizing will happen. */
  private var threshold = initSize * ThresholdRatio

  /** The array holding the servers. */
  private var keys = new Array[States](initSize)

  /** The array holding hash values. */
  private var hashes = new Array[Int](initSize)

  /** Hash States. */
  private def mkHash(sts: States): Int = {
    var h = sts(0).hashCode; var i = 1
    while(i < sts.length){ h = h*73 + sts(i).hashCode; i += 1 }
    // h ^= ((h >>> 20) ^ (h >>> 12))
    // (h >>> 7) ^ (h >>> 4)
    h
  }

  /** Find the index in the arrays corresponding to k. */
  private def find(k: States): Int = find(k, mkHash(k))

  /** Find the index in the arrays corrresponding to k with hash h. */ 
  @inline private def find(k: States, h: Int): Int = {
    var i = h & mask
    while(keys(i) != null && 
            (hashes(i) != h || keys(i) != k && !keys(i).sameElements(k)) )
//            !(hashes(i) == h && (keys(i) == k || keys(i).sameElements(k))) )
      i = (i+1)&mask
    i
  }

  /** The array holding the corresponding ComponentViews. */
  private var data = new Array[Boolean](initSize)

  /** Optionally get the value associated with k. */
  def get(k: States): Option[Boolean] = synchronized{
    val i = find(k)
    if(keys(i) == null) None
    else Some(data(i))
  }

  /** Add the mapping k -> b. */
  def add(k: States, b: Boolean): Unit = synchronized{
    if(count >= threshold){ resize(); add(k, b) }
    else{
      val h = mkHash(k); val i = find(k, h)
      if(keys(i) == null){
        keys(i) = k; data(i) = b; hashes(i) = h; count += 1
      }
      else  // Another thread has filled this slot in the same way.
        assert(keys(i).sameElements(k) && data(i) == b, 
          s"keys(i) = ${keys(i)}; k = $k; data(i) = ${data(i)}; b = $b" )
    }
  }

  /** Resize the hash table. */
  private def resize(): Unit = {
    // println("resizing")
    val oldKeys = keys; val oldData = data; val oldHashes = hashes; val oldN = n
    n += n; threshold = n * ThresholdRatio; mask = n-1
    keys = new Array[States](n); data = new Array[Boolean](n)
    hashes = new Array[Int](n); var i = 0
    while(i < oldN){
      val k = oldKeys(i)
      if(k != null){ // copy across
        val j = find(k); keys(j) = k
        data(j) = oldData(i); hashes(j) = oldHashes(i)
      }
      i += 1
    }
  }
}
