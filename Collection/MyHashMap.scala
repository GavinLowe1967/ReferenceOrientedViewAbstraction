package ViewAbstraction.collection

import ViewAbstraction.{hashOf,checkPow2}

/** A HashMap, mapping from A to B. */
trait MyHashMap[A,B]{
  /** Get the value associated with a, if one exits; otherwise update it
    * to the value of b. */
  def getOrElseUpdate(a: A, b: => B): B

  def size: Int

  def apply(a: A): B
}

// =======================================================

import scala.collection.mutable.Map

// class SimpleHashMap[A,B] extends MyHashMap[A,B]{
//   /** The underlying map. */
//   private val underlying = Map[A,B]()

//   /** Get the value associated with a, if one exits; otherwise update it
//     * to the value of b. */
//   def getOrElseUpdate(a: A, b: => B): B =
//     synchronized{ underlying.getOrElseUpdate(a, b) }

//   def size = underlying.size
// }

// =======================================================


// =======================================================

/** An implementation of MyHashMap that provides lock-free reads of
  * existing values.  This is designed to give good performance when
  * new values are quite rare. */
class MyLockFreeReadHashMap
  [A: scala.reflect.ClassTag, B: scala.reflect.ClassTag](initLength: Int = 64)
    extends MyHashMap[A,B]{

  checkPow2(initLength)

  /** Maximum load factor before resizing. */
  private val MaxLoad = 0.5

  /** Objects encapsulating the state. */
  private class TableState(val n: Int){
    /** The hashes of the mapping. */
    val hashes = new java.util.concurrent.atomic.AtomicIntegerArray(n)

    /** The states of the individual servers. */
    val keys = new Array[A](n)

    /** The corresponding ServerState objects. */
    val values = new Array[B](n)

    /** Bit mask to produce a value in [0..n). */
    val mask = n-1

    /** Find the position at which element (cs,ids) with hash h is stored
      * or should be placed. */
    @inline def find(a: A, h: Int) : Int = {
      var i = h & mask
      while({ val h1 = hashes.get(i); h1 != 0 && (h1 != h || keys(i) != a) })
        i = (i+1) & mask // (i+1)%n
      i
    }

    /* This represents the mapping
     * { keys(i) -> values(i) | hashes(i) != 0 }.
     * 
     * Each element is placed in the first empty (null) position
     * starting from its hash.  Its hash is placed in the
     * corresponding position in hashes.  Each entry is published when
     * its hash is written. */
  }

  /** The state of the table. */
  @volatile private var state = new TableState(initLength)

  /** The current number of entries. */
  private var count = 0

  /** The number of elements in this. */
  def size = count

  /** Threshold at which resizing should be performed. */
  private var threshold = (initLength*MaxLoad).toInt

  /** Resize the hash table. */
  @inline private def resize(oldState: TableState): TableState = {
    val oldN = oldState.n; val newState = new TableState(oldN*2)
    // println("ServerStates resize to "+oldN*2)
    threshold = 2*threshold
    val mask = newState.mask; var j = 0 // index into old arrays
    while(j < oldN){
      val h = oldState.hashes.get(j)
      if(h != 0){ // add oldState._(j) entries to new table
        var i = h & mask
        while(newState.hashes.get(i) != 0) i = (i+1) & mask 
        newState.keys(i) = oldState.keys(j)
        newState.values(i) = oldState.values(j)
        newState.hashes.set(i, h)
      }
      j += 1
    }
    state = newState // publish new state
    newState
  }

  /** Get the value associated with a, if one exits; otherwise update it
    * to the value of b. */
  def getOrElseUpdate(a: A, b: => B): B = {
    val h = hashOf(a); var myState = state // volatile read: subscribe
    var i = myState.find(a, h); val oldObj = myState.values(i)
    if(oldObj == null) synchronized{
      // Check state unchanged and no other thread wrote to i
      if(myState != state || myState.hashes.get(i) != 0)
        getOrElseUpdate(a, b) // retry
      else{
        if(count >= threshold){
          myState = resize(myState); i = myState.find(a, h)
        }
        // Store new ServerStates in position i
        // assert(myState.hashes.get(i) == 0 && myState.keys(i) == null)
        myState.keys(i) = a; val newObj = b; myState.values(i) = newObj
        myState.hashes.set(i, h) // publish update
        count += 1; newObj
      }
    } // end of synchronized block
    else if(myState.keys(i) == a) oldObj
    else getOrElseUpdate(a, b) // slot taken by another op; retry
  }

  /** Get the value associated with a.  Pre: such a value exists. */
  def apply(a: A): B = {
    val h = hashOf(a); var myState = state // volatile read: subscribe
    var i = myState.find(a, h); myState.values(i)
    // assert(b != null, "MyHashMap: key not found: "+a); b
  }

  /** Optionally get the value associated with a. */
  def get(a: A): Option[B] = {
    val h = hashOf(a); var myState = state // volatile read: subscribe
    var i = myState.find(a, h); val res = myState.values(i)
    if(res == null) None else Some(res)
  }
}
