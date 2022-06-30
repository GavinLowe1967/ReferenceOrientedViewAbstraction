package ViewAbstraction

import ox.gavin.profiling.Profiler
import scala.collection.mutable.{HashSet,HashMap}

/** A TransitionTemplate.  This represents a template pre U st -e-> post U st'
  * for every state st and st' such that (1) st and st' have identity id; (2)
  * st is compatible with pre; (3) if include then st -e-> st', otherwise st =
  * st'.  */
case class TransitionTemplate(
  pre: Concretization, post: Concretization, id: ProcessIdentity, 
  e: EventInt, include: Boolean){

  /** Map recording information about states that have been used to instantiate
    * this template.  A mapping st -> -1 indicates that st successfully
    * instantiated this template.  A mapping st -> ply indicates that st was
    * used unsuccessfully on ply ply. */
  private val doneExtend = new HashMap[State,Int]
  // IMPROVE: an array indexed by State ids might be better

  /** Record that st has been successfully used to instantiate this template. */
  def addDoneExtend(st: State) = synchronized{ doneExtend += st -> -1 }

  /** Has st been used to instantiate this template, either successfully or
    * previously on this ply? */
  def containsDoneExtend(st: State) = synchronized{ 
    doneExtend.get(st) match{
      case None => doneExtend += st -> ply; false
      case Some(p) => 
        if(p == -1 || p == ply) true
        else{ doneExtend += st -> ply; false }
    }
  }

}

object TransitionTemplateSet{
  /** A TransitionTemplate (pre, post, id, e, include) represents an extended
    * transition pre U st -e-> post U st' for every state st and st' such that
    * (1) st and st' have identity id; (2) st is compatible with pre; (3) if
    * include then st -e-> st', otherwise st = st'.  */ 
  // type TransitionTemplate = 
  //   (Concretization, Concretization, ProcessIdentity, EventInt, Boolean)
}

// ==================================================================
 
// import TransitionTemplateSet.TransitionTemplate

/** A set giving the transition templates seen so far. */
trait TransitionTemplateSet{
  /** Add template to the set. */
  def add(template: TransitionTemplate): Unit

  // /** An iterator over the set. */
  // def iterator: Iterator[TransitionTemplate]

  /** Does this contain temp? */
  def contains(temp: TransitionTemplate): Boolean

  /** An iterator giving just extended transitions where the pre-state matches
    * servers. */
  def iterator(servers: ServerStates) : Iterator[TransitionTemplate]

  def size: Long 
}

// ==================================================================

/*
/** A very simple (prototype) implementation of TransitionTemplateSet. */
class SimpleTransitionTemplateSet extends TransitionTemplateSet{
  /** A HashSet containing the transition templates. */
  private val set = new HashSet[TransitionTemplate]()

  /** Add the tuple (pre, post, id, e, include) to the set. */
  def add(pre: Concretization, post: Concretization, 
      id: ProcessIdentity, e: EventInt, include: Boolean) =
    set.add((pre, post, id, e, include))

  def contains(temp: TransitionTemplate) = set.contains(temp)

  /** An iterator over the set. */
  def iterator(servers: ServerStates): Iterator[TransitionTemplate] = 
    set.iterator.filter{ case (pre,_,_,_,_) => pre.servers == servers }

  def size = set.size
}
 */

// =====================================================================

import scala.collection.mutable.Set

/** An implementation of TransitionTemplateSet implemented as a map over the
  * ServerStates of the pre-state. */
class ServerBasedTransitionTemplateSet(initSize: Int = 16) 
    extends TransitionTemplateSet{

  checkPow2(initSize)

  /** The number of distinct ServerStates. */
  private var count = 0

  /** The number of TransitionTemplates. */
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
  private var transitions = new Array[Set[TransitionTemplate]](initSize)
  // IMPROVE: replace the Set[_] by something more efficient

  /** Find the index in the arrays corresponding to servers. */
  private def find(ss: ServerStates): Int = {
    var i = ss.hashCode & mask
    while(keys(i) != ss && keys(i) != null) i = (i+1)&mask
    i
  }

  /** Add template to the set. */
  def add(template: TransitionTemplate): Unit = {
    val servers = template.pre.servers; val i = find(servers)
    if(keys(i) == null){
      if(count >= threshold){ resize(); return add(template) }
      keys(i) = servers; transitions(i) = Set[TransitionTemplate](); count += 1
    }
    if(transitions(i).add(template)) theSize += 1
  }

  /** Resize the hash table. */
  private def resize(): Unit = {
    // println("resizing")
    val oldKeys = keys; val oldTrans = transitions; val oldSlots = slots
    slots += slots; threshold = slots * ThresholdRatio; mask = slots-1
    keys = new Array[ServerStates](slots)
    transitions = new Array[Set[TransitionTemplate]](slots)
    var i = 0
    while(i < oldSlots){
      val ss = oldKeys(i)
      if(ss != null){ // copy across
        val j = find(ss); keys(j) = ss; transitions(j) = oldTrans(i)
      }
      i += 1
    }
  }

  /** Does this contain temp? */
  def contains(temp: TransitionTemplate): Boolean = {
    val servers = temp.pre.servers; val i = find(servers)
    keys(i) != null && transitions(i).contains(temp)
  }


  /** An iterator giving just extended transitions where the pre-state matches
    * servers. */
  override def iterator(servers: ServerStates) : Iterator[TransitionTemplate] = {
    val i = find(servers); val set = transitions(i)
    if(set == null) Iterator.empty[TransitionTemplate] else set.iterator
  }

  def size = theSize
}
