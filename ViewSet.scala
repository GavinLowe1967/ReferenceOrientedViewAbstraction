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

  /** Iterator over all views matching servers and principal. */
  def iterator(servers: ServerStates, principal: State)
      : Iterator[ComponentView] =
    iterator(servers).filter(cv => cv.principal == principal)

  /** Get the representative of sv.  Used in debugging only.
    * Pre: this includes such a representative. */
  def getRepresentative(sv: ComponentView): ComponentView

  def summarise: String

  def summarise1: String = ???

  override def toString = iterator.toArray.map(_.toString).sorted.mkString("\n")

}

// =======================================================

object ViewSet{
  def apply(): ViewSet = new ServerPrincipalBasedViewSet(16)
  // new ServerBasedViewSet(16) // new CanonicalViewSet

  def apply(sizeEstimate: Int): ViewSet = new ServerBasedViewSet(sizeEstimate)
    // new CanonicalViewSet(sizeEstimate)
}

// =======================================================

// /** An implementation based on canonical forms.
//   * @param sizeEstimate an estimate of the number of elements this will 
//   * contain, if positive. */
// class CanonicalViewSet(sizeEstimate: Int = -1) extends ViewSet{
//   /** The set of system views.  
//     * Invariant: all members of underlying are in canonical form. */
//   private val underlying: MyHashSet[ComponentView] =
//     if(sizeEstimate <= 0) 
//       new LockFreeReadHashSet[ComponentView](shards = 2, MaxLoad = 0.7)
//       // (powerOf2AboveNumThreads*8)
//     else{
//       val shards = LockFreeReadHashSet.DefaultShards
//       val initLength = powerOfTwoAtLeast(sizeEstimate/shards) max 16
//       println("initLength = "+initLength)
//       new LockFreeReadHashSet[ComponentView](shards, initLength, 0.7)
//     }

//   /** Add sv to this. */
//   @inline def add(sv: ComponentView): Boolean = underlying.add(sv)

//   @inline def contains(sv: ComponentView): Boolean = underlying.contains(sv)

//   override def size = underlying.size

//   /** Iterator over the set. */
//   def iterator: Iterator[ComponentView] = underlying.iterator 

//   /** Get the representative of sv.  Used in debugging.
//     * Pre: this includes such a representative; and this operation is not 
//     * concurrent with any add operation. */
//   def getRepresentative(sv: ComponentView): ComponentView =  underlying.get(sv)
// }

// ==================================================================

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

    def next = { val d = data(ix); ix += 1; advance; d }
  } // end of iterator
} // end of BasicHashMap

// ==================================================================


import scala.collection.mutable.Set

/** An implementation of a ViewSet where views are stored by server. */
class ServerBasedViewSet(initSize: Int = 16) extends ViewSet{
  /** The BasicHashMap we use. */
  private val underlying = new BasicHashMap[ServerStates, Set[ComponentView]](
    initSize, Set[ComponentView]()
  )
  // Invariant: all the Set[ComponentView] are non-empty.

  /** The number of ComponentViews. */
  private var theSize = 0L

  /** Add sv to this. */
  def add(sv: ComponentView) : Boolean = {
    val views = underlying.getOrInit(sv.servers)
    if(views.add(sv)){ theSize += 1; true } else false
  }

  /** Does this contain sv? */
  def contains(sv: ComponentView): Boolean = {
    val set = underlying.get(sv.servers)
    set != null && set.contains(sv)
  }

  /** The number of elements in the set. */
  def size: Long = theSize

  /** Iterator over the set.  */
  def iterator : Iterator[ComponentView] = new Iterator[ComponentView]{
    /** An iterator over underlying, giving Set[ComponentView]s. */
    private val iter = underlying.iterator

    /** The current iterator over a Set[ComponentView]. */
    private var current: Iterator[ComponentView] = null

    def hasNext = 
      if(current != null && current.hasNext) true
      else if(iter.hasNext){
        current = iter.next.iterator; assert(current.hasNext); true 
      }
      else false

    def next = { assert(hasNext); current.next }
  } // end of iterator

  /** Iterator over all views matching servers. */
  override def iterator(servers: ServerStates) : Iterator[ComponentView] = {
    val set = underlying.get(servers)
    if(set == null) Iterator.empty[ComponentView] else set.iterator
  }

  /** Get the representative of sv.  Used in debugging only.
    * Pre: this includes such a representative. */
  def getRepresentative(sv: ComponentView): ComponentView = {
    // IMPROVE: using find is inefficient
    val set = underlying.get(sv.servers); set.find(_ == sv).get
  }

  def summarise = ???

  override def toString = iterator.toArray.map(_.toString).sorted.mkString("\n")
}

// =======================================================

/** An implementation of a set of Views, all with the same ServerStates.  This
  * allows efficient iteration over the views corresponding to a particular
  * principal.  Used in ServerPrincipalBasedViewSet. */
class PrincipalBasedViewSet(initSize: Int = 4){
  /** The underlying BasicHashMap, representing a mapping from principal states
    * to sets of Views. */
  private val underlying = new BasicHashMap[State, Set[ComponentView]](
    initSize, Set[ComponentView]())

  /** Add sv to this. */
  def add(sv: ComponentView) : Boolean = {
    val views = underlying.getOrInit(sv.principal)
    views.add(sv)
  }

  /** Does this contain sv? */
  def contains(sv: ComponentView): Boolean = {
    val set = underlying.get(sv.principal)
    set != null && set.contains(sv)
  }

  /** Iterator over the set.  */
  def iterator : Iterator[ComponentView] = new Iterator[ComponentView]{
    /** An iterator over underlying, giving Set[ComponentView]s. */
    private val iter = underlying.iterator

    /** The current iterator over a Set[ComponentView]. */
    private var current: Iterator[ComponentView] = null

    def hasNext = 
      if(current != null && current.hasNext) true
      else if(iter.hasNext){
        current = iter.next.iterator; assert(current.hasNext); true 
      }
      else false

    def next = { assert(hasNext); current.next }
  } // end of iterator

  /** Iterator over all views matching principal. */
  def iterator(principal: State): Iterator[ComponentView] = {
    val set = underlying.get(principal)
    if(set == null) Iterator.empty[ComponentView] else set.iterator
  }

  /** Get the representative of sv.  Used in debugging only.
    * Pre: this includes such a representative. */
  def getRepresentative(sv: ComponentView): ComponentView = {
    // IMPROVE: using find is inefficient
    underlying.get(sv.principal).find(_ == sv).get
  }

  /** An iterator giving a summary for each principal. */
  def summarise: Iterator[String] = 
    underlying.iterator.map(set => 
      set.head.toString0+": "+set.size// +
        // (if(set.size > 100) 
        //   set.iterator.toArray.map(_.toString0).sorted.mkString("\n\t")
        // else "")
    )

  /** An iterator giving a summary for each principal. */
  def summarise1: String = {
    val sets = underlying.iterator.toArray
    // Summary by principals
    val st1 = 
      sets.map(set => set.head.toString0+": "+set.size).sorted.mkString("\n")
    // List the largest set
    val max: Set[ComponentView] = sets.maxBy(_.size)
    val st2 = max.toArray.map(_.toString0).sorted.mkString("\n\t")
    st1+"\n\n"+st2
  }

  /** The number of elements in this.  
    * Note: inefficient. */
  def size = underlying.iterator.map(_.size).sum

  override def toString = iterator.toArray.map(_.toString).sorted.mkString("\n")
}

// =======================================================

/** An implementation of a ViewSet where views are stored by server and
  * principal. */
class ServerPrincipalBasedViewSet(initSize: Int = 16) extends ViewSet {
  /** The underlying BasicHashMap, representing a mapping from ServerStates to
    * PrincipalBasedViewSets. */
  private val underlying = new BasicHashMap[ServerStates, PrincipalBasedViewSet](
    initSize, new PrincipalBasedViewSet()
  )

  /** The number of ComponentViews. */
  private var theSize = 0L

  /** Add sv to this. */
  def add(sv: ComponentView) : Boolean = {
    val views = underlying.getOrInit(sv.servers)
    if(views.add(sv)){ theSize += 1; true } else false
  }

  /** Does this contain sv? */
  def contains(sv: ComponentView): Boolean = {
    val set = underlying.get(sv.servers)
    set != null && set.contains(sv)
  }

  /** The number of elements in the set. */
  def size: Long = theSize

  /** Iterator over the set.  */
  def iterator : Iterator[ComponentView] = new Iterator[ComponentView]{
    /** An iterator over underlying, giving Set[ComponentView]s. */
    private val iter = underlying.iterator

    /** The current iterator over a Set[ComponentView]. */
    private var current: Iterator[ComponentView] = null

    def hasNext = 
      if(current != null && current.hasNext) true
      else if(iter.hasNext){
        current = iter.next.iterator; assert(current.hasNext); true 
      }
      else false

    def next = { assert(hasNext); current.next }
  } // end of iterator


  /** Iterator over all views matching servers. */
  override def iterator(servers: ServerStates) : Iterator[ComponentView] = {
    val set = underlying.get(servers)
    if(set == null) Iterator.empty[ComponentView] else set.iterator
  }

  /** Iterator over all views matching servers and principal. */
  override def iterator(servers: ServerStates, principal: State)
      : Iterator[ComponentView] = {
    val set = underlying.get(servers)
    if(set == null) Iterator.empty[ComponentView] else set.iterator(principal)
  }

  /** Get the representative of sv.  Used in debugging only.
    * Pre: this includes such a representative. */
  def getRepresentative(sv: ComponentView): ComponentView = {
    underlying.get(sv.servers).getRepresentative(sv)
  }

  def summarise: String = 
    underlying.iterator.flatMap(_.summarise).toArray.sorted.mkString("\n")

  /** A brief summary. 
    * The summary gives the number of Views for each ServerSet, and expands the largest. */
  override def summarise1: String = {
    val sets = underlying.iterator.toArray
    // Summary by servers
    val st0 = 
      sets.map(pbvs => pbvs.iterator.next.toString+": "+pbvs.size).
        sorted.mkString("\n")
    // The largest such
    val max: PrincipalBasedViewSet = sets.maxBy(_.size)
    val st1 = max.summarise1 //.toArray.map(_.toString).sorted.mkString("\n")
    st0+"\n\n"+st1
  }

  override def toString = iterator.toArray.map(_.toString).sorted.mkString("\n")

  // import java.lang.reflect.Modifier
  // import ox.gavin.profiling._
  // import ox.gavin.profiling.MemoryProfiler.traverse  
  // def memoryProfile = {
  //   traverse("sysAbsViews", underlying)
  // }
}
