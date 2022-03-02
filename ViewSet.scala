package ViewAbstraction

import scala.collection.mutable.{HashMap,HashSet}

/** A set of system views. */
trait ViewSet{
  /** Add sv to this. */
  def add(sv: ComponentView) : Boolean

  /** Does this contain sv? */
  def contains(sv: ComponentView): Boolean 

  /** Does this contain a view corresponding to servers and cpts? */
  def contains(servers: ServerStates, cpts: Array[State]): Boolean

  /** Get the view in this corresponding to v.  Pre: there is one. */
  def get(v: ComponentView): ComponentView 

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
  //def getRepresentative(sv: ComponentView): ComponentView

  def summarise: String

  def summarise1: String = ???

  override def toString = iterator.toArray.map(_.toString).sorted.mkString("\n")

}

// =======================================================

object ViewSet{
  def apply(): ViewSet = new ServerPrincipalBasedViewSet(16)
}

// =======================================================

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

/** A set of views, all of which have the same servers and principal. */
class ComponentsSet(initSize: Int = 4){
  checkPow2(initSize)

  /* The set is implemented as a hash set. */ 

  /** The hash of the servers associated with this set.  Set by the first
    * add. */
  private var hashBase = -1

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

  /** The views themselves. */
  private var views = new Array[ComponentView](initSize)

  /** Find the index in views corresponding to v. */
  @inline private def find(v: ComponentView): Int = 
    find1(v.hashCode, v.components)

  /** Find the index in views corresponding to cpts. */
  @inline private def find(cpts: Array[State]): Int = 
    find1(StateArray.mkHash(hashBase, cpts), cpts)
    // Note: the above is a little inefficient: all elements in this set have
    // the same cpts(0).

  /** Find the index in views corresponding to cpts, with corresponding hash h:
    * either where a view with cpts appears, or the first space after
    * h&mask. */
  @inline private def find1(h: Int, cpts: Array[State]): Int = {
    var i = h & mask
    while(views(i) != null && !views(i).components.sameElements(cpts))
      i = (i+1) & mask
    // IMPROVE: it's enough to compare the components from index 1
    i
  }

  /** Add v to this. */
  def add(v: ComponentView) : Boolean = {
    if(count == 0) hashBase = v.servers.hashCode
    val i = find(v)
    if(views(i) == null){ 
      if(count >= threshold){ resize(); add(v) }
      else{ views(i) = v; count += 1; true }
    }
    else false
  }

  /** Resize the hash table. */
  def resize() = {
    val oldViews = views; val oldN = n
    n += n; threshold = n * ThresholdRatio; mask = n-1
    views = new Array[ComponentView](n); var i = 0
    while(i < oldN){
      val v = oldViews(i)
      if(v != null){ val j = find(v); views(j) = v }
      i += 1
    }
  }

  /** Does this contain a view with components `cpts`? */
  def contains(cpts: Array[State]): Boolean = {
    require(count > 0); val i = find(cpts); views(i) != null
  }

  /** Get the view in this corresponding to v. */
  def get(v: ComponentView): ComponentView = {
    require(count > 0); val i = find(v); assert(views(i) == v); views(i)
  }

  /** Iterator over the contents of this. */
  def iterator : Iterator[ComponentView] = new Iterator[ComponentView]{
    /** The index of the next value to return. */
    private var ix = 0

    /** Advance to the next value. */
    private def advance = while(ix < n && views(ix) == null) ix += 1

    advance

    def hasNext = ix < n

    def next = { val d = views(ix); ix += 1; advance; d }
  } // end of iterator


  /** The size of this set. */
  def size: Int = count

  /** An arbitrary member of this set. */
  def head: ComponentView = {
    require(count > 0)
    var i = 0
    while(i < n && views(i) != null) i += 1
    assert(i < n); views(i)
  }
}

// =======================================================

/** An implementation of a set of Views, all with the same ServerStates.  This
  * allows efficient iteration over the views corresponding to a particular
  * principal.  Used in ServerPrincipalBasedViewSet. */
class PrincipalBasedViewSet(initSize: Int = 4){
  /** The underlying BasicHashMap, representing a mapping from principal states
    * to sets of Views. */
  private val underlying = new BasicHashMap[State, ComponentsSet](
    initSize, new ComponentsSet)

  /** Add sv to this. */
  def add(sv: ComponentView) : Boolean = {
    val views = underlying.getOrInit(sv.principal)
    views.add(sv)
  }

  /** Does this contain sv? */
  def contains(sv: ComponentView): Boolean = {
    val set = underlying.get(sv.principal)
    set != null && set.contains(sv.components)
  }

  /** Does this contain a view corresponding to cpts? */
  def contains(cpts: Array[State]): Boolean = {
    val set = underlying.get(cpts(0))
    set != null && set.contains(cpts) 
  }

  /** Get the view in this corresponding to v.  Pre: there is one. */
  def get(v: ComponentView): ComponentView = 
    underlying.get(v.principal).get(v)

  /** Iterator over the set.  */
  def iterator : Iterator[ComponentView] = new Iterator[ComponentView]{
    /** An iterator over underlying, giving ComponentsSets. */
    private val iter = underlying.iterator

    /** The current iterator over a ComponentsSet. */
    private var current: Iterator[ComponentView] = null

    def hasNext = 
      if(current != null && current.hasNext) true
      else if(iter.hasNext){
        // Move onto next element in underlying
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
  // def getRepresentative(sv: ComponentView): ComponentView = 
  //   underlying.get(sv.principal).get(sv) 

  /** An iterator giving a summary for each principal. */
  def summarise: Iterator[String] = 
    underlying.iterator.map(set => 
      set.head.toString0+": "+set.size
    )

  /** An iterator giving a summary for each principal. */
  def summarise1: String = {
    val sets = underlying.iterator.toArray
    // Summary by principals
    val st1 = 
      sets.map(set => set.head.toString0+": "+set.size).sorted.mkString("\n")
    // List the largest set
    val max: ComponentsSet = sets.maxBy(_.size)
    val st2 = max.iterator.toArray.map(_.toString0).sorted.mkString("\n\t")
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

  /** Does this contain a view corresponding to servers and cpts? */
  def contains(servers: ServerStates, cpts: Array[State]): Boolean = {
    val set = underlying.get(servers)
    set != null && set.contains(cpts)
  }

  /** Get the view in this corresponding to v.  Pre: there is one. */
  def get(v: ComponentView): ComponentView = 
    underlying.get(v.servers).get(v)

  /** The number of elements in the set. */
  def size: Long = theSize

  /** Iterator over the set.  */
  def iterator : Iterator[ComponentView] = new Iterator[ComponentView]{
    /** An iterator over underlying, giving PrincipalBasedViewSets. */
    private val iter = underlying.iterator

    /** The current iterator over a PrincipalBasedViewSet. */
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
  // def getRepresentative(sv: ComponentView): ComponentView = {
  //   underlying.get(sv.servers).getRepresentative(sv)
  // }

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
    val st1 = max.summarise1 
    st0+"\n\n"+st1
  }

  override def toString = iterator.toArray.map(_.toString).sorted.mkString("\n")

}
