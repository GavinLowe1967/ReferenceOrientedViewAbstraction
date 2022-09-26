package ViewAbstraction.collection

import ox.gavin.profiling.Profiler

/** A set of non-zero Ints.  The implementation aims to be very compact, at
  * least with small sets.  Not thread-safe. */ 
class IntSet{
  import IntSet.{MaxContiguousSize, ThresholdRatio, FirstHashSetSize}

  /* The implementation goes through four stages:
   * - Empty set: elements = null and n = 0;
   * - Singleton set {x} with x != 0: elements = 0 and n = x;
   * - Size in range [2..MaxContiguousSize), members of set stored contiguously 
   *   in elements, in sorted order;
   * - Size at least MaxContiguousSize: elements used as a hash set, with n the
   *   number of elements.  */

  /** Number of elements.  Equal to elements.size during the contiguous
    * phase. */
  private var n = 0

  /** Array holding the elements.  */
  private var elements: Array[Int] = null //  = new Array[Int](0)

  /** Try to add x to the set.  Return true if x was not already in the set. */
  def add(x: Int): Boolean = {
    require(x != 0)
    if(elements == null){
      if(n == 0){ n = x; true } // move to singleton stage
      else if(n != x){ // move to contiguous state
        if(n < x) elements = Array(n,x) else elements = Array(x,n)
        n = 2; true
      }
      else false // x matches element of singleton set
    }
    else if(n <= MaxContiguousSize) addContiguous(x) 
    else addToHashSet(x)
  }

  /** Add x, while in contiguous mode. */
  @inline private def addContiguous(x: Int) = {
    var i = 0; assert(n == elements.size)
    // Search for x.  IMPROVE: use binary search
    while(i < n && elements(i) < x) i += 1
    if(i < n && elements(i) == x) false
    else if(n < MaxContiguousSize){
      // elements[0..i) < x < elements[i..n)
      val newEls = new Array[Int](n+1); var j = 0
      // copy elements[0..i) into newEls[0..i)
      while(j < i){ newEls(j) = elements(j); j += 1 }
      newEls(i) = x
      // copy elements[i..n) into newEls[i+1..n+1)
      while(i < n){ newEls(i+1) = elements(i); i += 1 }
      elements = newEls; n += 1; true
    }
    else{  // Switch to hash set mode
      convertToHashSet; assert(n == MaxContiguousSize); addToHashSet(x)
    }
  }

  /** Convert into hash set mode. */
  private def convertToHashSet = {
    Profiler.count("IntSet.convert")
    val oldEls = elements; elements = new Array[Int](FirstHashSetSize)//; n = 0
    var i = 0
    while(i < oldEls.size){ addToTable(oldEls(i)); i += 1 }
    // IMPROVE: this could be done using a specialised variant of addTohashSet.
  }

  /** Add x to the table.  This assumes it is not already there.  Used during
    * conversion to hash set mode and when resizing.  Note that n is not
    * updated.  */
  @inline private def addToTable(x: Int) = { 
    require(x != 0); val mask = elements.size-1; var i = x & mask
    while(elements(i) != 0) i = (i+1)&mask
    elements(i) = x
  }

  /** Add x, while in hash set mode. */
  @inline private def addToHashSet(x: Int) : Boolean = { 
    if(n >= elements.size*ThresholdRatio) resize()
    val mask = elements.size-1; var i = x & mask
    while(elements(i) != 0 && elements(i) != x) i = (i+1)&mask
    if(elements(i) == 0){ elements(i) = x; n += 1; true }
    else false
  }

  /** Resize the hash table. */
  private def resize() = {
    Profiler.count("IntSet.resize")
    val oldEls = elements; elements = new Array(oldEls.size*2); var i = 0
    while(i < oldEls.size){
      val x = oldEls(i); i += 1; if(x != 0) addToTable(x)
    }
  }
}

// =======================================================

object IntSet{
  /** The maximum size before we switch to using a HashSet. */
  private val MaxContiguousSize = 80

  // Note: the above figure is a bit of a finger-in-the-air.  Too large will
  // make addContiguous inefficient.  But smaller will lead to more memory
  // usage.

  /** The maximum load factor while in hash set mode: we resize when this load
    * factor is reached. */
  private val ThresholdRatio = 0.5F

  /** The initial size to use for the array when we switch to hash set mode. */
  private val FirstHashSetSize = 256

  ViewAbstraction.checkPow2(FirstHashSetSize)

  assert(FirstHashSetSize * ThresholdRatio > MaxContiguousSize)


}
 
