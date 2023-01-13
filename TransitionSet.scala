package ViewAbstraction

import scala.collection.mutable.HashSet

/** A set recording the transitions seen so far. 
  * 
  * contains and iterator need to be thread-safe; add and size are called only
  * sequentially. */
trait TransitionSet{
  /** Add the transition t. */
  def add(t: Transition): Boolean

  /** An iterator over the transitions. */
  def iterator(servers: ServerStates): Iterator[Transition]

  def size: Long

  def contains(trans: Transition): Boolean
}


// ==================================================================

/*
/** A very simple (prototype) implementation of TransitionSet. */
class SimpleTransitionSet extends TransitionSet{

  /** A HashSet containing the transitions. */
  private val set = new HashSet[Transition]()

  /** Add the transition pre -> post. */
  def add(pre: Concretization, e: EventInt, post: Concretization) = 
    set.add((pre, e, post))

  // /** An iterator over the transitions. */
  // def iterator = set.iterator 

  /** An iterator over the transitions. */
  def iterator(servers: ServerStates): Iterator[Transition] = 
     set.iterator.filter{ _.servers == servers } // case (pre,_,_) => pre.servers == servers }

  def size = set.size

  def contains(trans: Transition) = set.contains(trans)
}
 */ 

// =====================================================================

/*
import scala.collection.mutable.Set

/** An implementation of TransitionTemplateSet implemented as a map over the
  * ServerStates of the pre-state. */
class ServerBasedTransitionSet(initSize: Int = 16) extends TransitionSet{
  checkPow2(initSize)

  /** The number of distinct ServerStates. */
  private var count = 0

  /** The number of ComponentViews. */
  private var theSize = 0L

  /** The number of slots in the hash table. */
  private var slots = initSize

  /** A bitmask to produce a value in [0..slts). */
  private var mask = slots-1

  /** The threshold ratio at which resizing happens. */
  private val ThresholdRatio = 0.7

  /** The threshold at which the next resizing will happen. */
  private var threshold = initSize * ThresholdRatio

  /** The array holding the servers. */
  private var keys = new Array[ServerStates](initSize)

  /** The array holding the corresponding TransitionTemplates. */
  private var transitions = new Array[Set[Transition]](initSize)
  // IMPROVE: replace the Set[_] by something more efficient

  /** Find the index in the arrays corresponding to servers. */
  private def find(ss: ServerStates): Int = {
    var i = ss.hashCode & mask
    while(keys(i) != ss && keys(i) != null) i = (i+1)&mask
    i
  }

  /** Add the transition t to the set. */
  def add(t: Transition): Boolean = {
    val servers = t.pre.servers; val i = find(servers)
    if(keys(i) == null){
      if(count >= threshold){ resize(); return add(t) }
      keys(i) = servers; transitions(i) = Set[Transition](); count += 1
    }
    if(transitions(i).add(t)){ theSize += 1; true }
    else false
  }

  /** Resize the hash table. */
  private def resize(): Unit = { 
    // println("resizing"); 
    val oldKeys = keys; val oldTrans = transitions; val oldSlots = slots
    slots += slots; threshold = slots * ThresholdRatio; mask = slots-1
    keys = new Array[ServerStates](slots)
    transitions = new Array[Set[Transition]](slots)
    var i = 0
    while(i < oldSlots){
      val ss = oldKeys(i)
      if(ss != null){ // copy across
        val j = find(ss); assert(keys(j) == null)
        keys(j) = ss; transitions(j) = oldTrans(i)
      }
      i += 1
    }
  }

  /** An iterator giving just extended transitions where the pre-state matches
    * servers. */
  override def iterator(servers: ServerStates) : Iterator[Transition] = {
    val i = find(servers); val set = transitions(i)
    if(set == null) Iterator.empty[Transition] 
    // else if(TransitionSet.reversed) set.iterator.toArray.reverse.iterator 
    else set.iterator
  }

  def size = theSize

  def contains(trans: Transition) = {
    val servers = trans.pre.servers; val i = find(servers)
    keys(i) != null && transitions(i).contains(trans)
  }
}


object TransitionSet{
  // Should the iterator be reversed.
  // var reversed = false
}
 */
