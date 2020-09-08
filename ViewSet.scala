package ViewAbstraction

import scala.collection.mutable.{HashMap,HashSet}

/** A set of system views. */
trait ViewSet{
  /** Add sv to this. */
  def add(sv: View) : Boolean

  /** Add a sequence of elements to the set. */
  def add (ss: Seq[View]) : Unit = for(s <- ss) add(s)

  /** Add elements of iterator to the set. */
  def add (ss: Iterator[View]) : Unit = for(s <- ss) add(s)

  /** Does this contain sv? */
  def contains(sv: View): Boolean

  /** The number of elements in the set. */
  def size: Long 

  def reportSizes = Array(size)

  /** Iterator over the set.  Not thread safe. */
  protected def iterator : Iterator[View] 

  /** List of the elements of the set.  Not thread safe. */
  def toList : List[View] = iterator.toList 

  def toArray: Array[View] = iterator.toArray

  /** Make a string representing the set, separating elements using seq. */
  def mkString(sep: String) = toList.mkString(sep)

  /** Get the representative of sv.  Used in debugging only.
    * Pre: this includes such a representative. */
  def getRepresentative(sv: View): View

  /** Add inc to the current count. */
  def addCount(inc: Int): Unit

}

// =======================================================

object ViewSet{
  def apply(): ViewSet = new CanonicalViewSet

  def apply(sizeEstimate: Int): ViewSet = 
    new CanonicalViewSet(sizeEstimate)
}



// =======================================================

/** An implementation based on canonical forms.
  * @param sizeEstimate an estimate of the number of elements this will contain, if 
  * positive. */
class CanonicalViewSet(sizeEstimate: Int = -1) extends ViewSet{
  /** The set of system views.  
    * Invariant: all members of underlying are in canonical form. */
  private val underlying: MyHashSet[View] =
    if(sizeEstimate <= 0) new LockFreeReadHashSet[View](MaxLoad = 0.7) 
      // (powerOf2AboveNumThreads*8)
    // new MyShardedHashSet[View]
    else{
      val shards = LockFreeReadHashSet.DefaultShards
      val initLength = powerOfTwoAtLeast(sizeEstimate/shards) max 16
      println("initLength = "+initLength)
      new LockFreeReadHashSet[View](shards, initLength, 0.7)
    }

  /** Add sv to this. */
  @inline def add(sv: View): Boolean = {
    // println(s"add($sv)")
    underlying.add(sv)
  }

  @inline def contains(sv: View): Boolean = underlying.contains(sv)

  override def size = underlying.size

  override def reportSizes = underlying.reportSizes

  /** Iterator over the set. */
  protected def iterator: Iterator[View] = underlying.iterator 

  /** Get the representative of sv.  Used in debugging.
    * Pre: this includes such a representative; and this operation is not 
    * concurrent with any add operation. */
  def getRepresentative(sv: View): View =  underlying.get(sv)

  def addCount(inc: Int) = ???

}

// =======================================================

/** A ViewSet corresponding to gamma_aShapes(absViews), i.e. all views
  * that are abstractions of absViews. */
class ImplicitViewSet(absViews: ViewSet, aShapes: List[Shape]) 
extends ViewSet{
  /** Are we currently testing the implementation, using an explicit shadow set?
    * Note, in order to use this, it is necessary to disable recycling of
    * Views (View.returnView), and ensure
    * NewViewExtender.extensions always calls this.add.  Calls to shadowSize
    * should then give the expected number of states. */  
  // private val Testing = true // false

  // private val shadow = 
  //   if(Testing)  new scala.collection.mutable.HashSet[View]
  //   else null

  /** The number of views implicitly in this set. */
  private val count = new java.util.concurrent.atomic.AtomicLong

  /** Add sv to this. */
  def add(sv: View): Boolean = { ???
    // // Iterate over all elements of alpha(sv)
    // // IMPROVE: replace vs by an iterator, so as to be lazier
    // val cpts = sv.componentView; val vs = Views.alpha(aShapes, cpts)
    // Views.returnView(cpts)
    // // done is true if we have found a member of alpha(sv) not in absViews
    // var i = 0; var done = false
    // while(i < vs.length){
    //   val v1 = vs(i)
    //   if(!done){
    //     val abs = View.mkView(sv.servers, v1)
    //     done = !absViews.contains(abs)
    //     View.returnView(abs)
    //   }
    //   i += 1; Views.returnView(v1) 
    // }
    // if(done){ count.getAndIncrement; true }
    // else false
  }

  // def shadowSize = shadow.size

  def addCount(inc: Int) = count.getAndAdd(inc)

  def size: Long = count.get

  def getRepresentative(sv: View): View = ???

  protected def iterator: Iterator[View] = ???

  def contains(sv: View): Boolean = ???
}


// =======================================================

/** A Sequential implementation, using open addressing. */
class SeqViewSet(initLength: Int = 16) extends ViewSet{
  checkPow2(initLength)

  /** The number of slots in the hash table. */
  private var length = initLength

  private var hashes = new Array[Int](length)

  private var elements = new Array[View](length)

  /** The number of elements in the hash table. */
  private var theSize = 0

  private val MaxLoad = 0.7

  /** Bitmask for item in [0..length). */
  private var mask = length-1

  /** Threshold for resizing. */
  private var threshold = (length*MaxLoad).toInt

  def add(sv: View) = {
    val h = hashOf(sv)
    if(theSize >= threshold) resize
    var i = h&mask
    while(hashes(i) != 0 && (hashes(i) != h || elements(i) != sv))
      i = (i+1)&mask
    if(hashes(i) == h) false // { assert(elements(i) == sv); false } 
    else{
      // assert(hashes(i) == 0 && elements(i) == null)
      hashes(i) = h; elements(i) = sv; theSize += 1; true
    }
  }

  private def resize = {
    val oldLength = length; length = 2*length
    val oldHashes = hashes; hashes = new Array[Int](length)
    val oldElements = elements; elements = new Array[View](length)
    mask = length-1; threshold = (length*MaxLoad).toInt
    var i = 0
    while(i < oldLength){
      val h = oldHashes(i)
      if(h != 0){
        var j = h&mask
        while(hashes(j) != 0) j = (j+1)&mask
        hashes(j) = h; elements(j) = oldElements(i)
      }
      // else assert(oldElements(i) == null)
      i += 1
    }

  }

  def addCount(inc: Int): Unit = ???
  def contains(sv: View): Boolean = ???
  def getRepresentative(sv: View): View = ???
  protected def iterator: Iterator[View] = ???

  def shadowSize = ???
  def size: Long = theSize.toLong

}
