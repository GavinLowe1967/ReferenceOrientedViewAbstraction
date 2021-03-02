package ViewAbstraction

import scala.collection.mutable.{HashMap,HashSet}

/** A set of system views. */
trait ViewSet{
  /** Add sv to this. */
  def add(sv: ComponentView) : Boolean

  /** Does this contain sv? */
  def contains(sv: ComponentView): Boolean

  /** The number of elements in the set. */
  def size: Long 

  /** Iterator over the set.  Not thread safe. */
  def iterator : Iterator[ComponentView] 

  /** Iterator over all views matching servers. */
  def iterator(servers: ServerStates) : Iterator[ComponentView] =
    iterator.filter(cv => cv.servers == servers)

  /** Get the representative of sv.  Used in debugging only.
    * Pre: this includes such a representative. */
  def getRepresentative(sv: ComponentView): ComponentView

  override def toString = iterator.toArray.map(_.toString).sorted.mkString("\n")
}

// =======================================================

object ViewSet{
  def apply(): ViewSet = new ServerBasedViewSet(16) // new CanonicalViewSet

  def apply(sizeEstimate: Int): ViewSet = new ServerBasedViewSet(sizeEstimate)
    // new CanonicalViewSet(sizeEstimate)
}

// =======================================================

/** An implementation based on canonical forms.
  * @param sizeEstimate an estimate of the number of elements this will 
  * contain, if positive. */
class CanonicalViewSet(sizeEstimate: Int = -1) extends ViewSet{
  /** The set of system views.  
    * Invariant: all members of underlying are in canonical form. */
  private val underlying: MyHashSet[ComponentView] =
    if(sizeEstimate <= 0) 
      new LockFreeReadHashSet[ComponentView](shards = 2, MaxLoad = 0.7)
      // (powerOf2AboveNumThreads*8)
    else{
      val shards = LockFreeReadHashSet.DefaultShards
      val initLength = powerOfTwoAtLeast(sizeEstimate/shards) max 16
      println("initLength = "+initLength)
      new LockFreeReadHashSet[ComponentView](shards, initLength, 0.7)
    }

  /** Add sv to this. */
  @inline def add(sv: ComponentView): Boolean = {
    // println(s"add($sv)")
    underlying.add(sv)
  }

  @inline def contains(sv: ComponentView): Boolean = underlying.contains(sv)

  override def size = underlying.size

  // def reportSizes = underlying.reportSizes

  /** Iterator over the set. */
  def iterator: Iterator[ComponentView] = underlying.iterator 

  /** Get the representative of sv.  Used in debugging.
    * Pre: this includes such a representative; and this operation is not 
    * concurrent with any add operation. */
  def getRepresentative(sv: ComponentView): ComponentView =  underlying.get(sv)

  // def addCount(inc: Int) = ???

}

// ==================================================================

import scala.collection.mutable.Set

/** An implementation of a ViewSet where views are stored by server. */
class ServerBasedViewSet(initSize: Int = 16) extends ViewSet{
  checkPow2(initSize)

  private val sbvs = this // For reference in the iterator

  /* At the top level, the ViewSet stores a mapping from ServerStates to sets of
   * Views, implemented as a hash map. */

  /** The number of distinct ServerStates. */
  private var count = 0

  /** The number of ComponentViews. */
  private var theSize = 0L

  /** The number of slots in the hash table. */
  private var length = initSize

  /** A bitmask to produce a value in [0..length). */
  private var mask = length-1

  /** The threshold ratio at which resizing happens. */
  private val ThresholdRatio = 0.7

  /** The threshold at which the next resizing will happen. */
  private var threshold = initSize * ThresholdRatio

  /** The array holding the servers. */
  private var keys = new Array[ServerStates](initSize)

  /** The array holding the corresponding ComponentViews. */
  private var views = new Array[Set[ComponentView]](initSize)
  // IMPROVE: replace the Set[ComponentView] by something more efficient

  /** Find the index in the arrays corresponding to servers. */
  private def find(ss: ServerStates): Int = {
    var i = ss.hashCode & mask
    while(keys(i) != ss && keys(i) != null) i = (i+1)&mask
    i
  }

  /** Add sv to this. */
  def add(sv: ComponentView) : Boolean = {
    val servers = sv.servers; val i = find(servers)
    if(keys(i) == null){
      if(count >= threshold){ resize(); return add(sv) }
      keys(i) = servers; views(i) = Set[ComponentView](); count += 1
    }
    if(views(i).add(sv)){ theSize += 1; true } else false
  }

  /** Resize the hash table. */
  private def resize(): Unit = {
    println("resizing")
    val oldKeys = keys; val oldViews = views; val oldLength = length
    length += length; threshold = length * ThresholdRatio; mask = length-1
    keys = new Array[ServerStates](length)
    views = new Array[Set[ComponentView]](length)
    var i = 0
    while(i < oldLength){
      val ss = oldKeys(i)
      if(ss != null){ // copy across
        val j = find(ss); keys(j) = ss; views(j) = oldViews(i)
      }
      i += 1
    }
  }

  /** Does this contain sv? */
  def contains(sv: ComponentView): Boolean = {
    val i = find(sv.servers); val set = views(i)
    set !=  null && set.contains(sv)
  }

  /** The number of elements in the set. */
  def size: Long = theSize

  /** Iterator over the set.  */
  def iterator : Iterator[ComponentView] = new Iterator[ComponentView]{
    private val n = sbvs.length 

    /** Index of the next set to iterate over. */
    private var ix = 0

    /** The current iterator, corresponding to views(i). */
    private var current: Iterator[ComponentView] = null

    /** Advance ix to the next set, and set current. */
    def advance = {
      while(ix < n && views(ix) == null) ix += 1
      if(ix < n) current = views(ix).iterator
    }

    advance

    def hasNext = 
      if(current == null) false
      else if(current.hasNext) true 
      else{ ix += 1; advance; ix < sbvs.length }

    def next = { assert(hasNext); current.next }
  } // end of iterator

  /** Iterator over all views matching servers. */
  override def iterator(servers: ServerStates) : Iterator[ComponentView] = {
    val i = find(servers); val set = views(i)
    if(set == null) Iterator.empty[ComponentView] else set.iterator
  }

  /** Get the representative of sv.  Used in debugging only.
    * Pre: this includes such a representative. */
  def getRepresentative(sv: ComponentView): ComponentView = {
    // IMPROVE: using find is inefficient
    val i = find(sv.servers); views(i).find(_ == sv).get
  }

  override def toString = 
    iterator.toArray.map(_.toString).sorted.mkString("\n")+
      s"\nNumber of ServerStates = $count"
}
