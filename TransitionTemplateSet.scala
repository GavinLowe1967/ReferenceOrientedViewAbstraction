package ViewAbstraction

import scala.collection.mutable.HashSet

object TransitionTemplateSet{
  /** A TransitionTemplate (pre, post, id, e, include) represents an extended
    * transition pre U st -e-> post U st' for every state st and st' such that
    * (1) st and st' have identity id; (2) st is compatible with pre; (3) if
    * include then st -e-> st', otherwise st = st'.  */ 
  type TransitionTemplate = 
    (Concretization, Concretization, ProcessIdentity, EventInt, Boolean)
}

// ==================================================================

/** A set giving the transition templates seen so far. */
trait TransitionTemplateSet{
  /** Add the tuple (pre, post, id, e, include) to the set. */
  def add(pre: Concretization, post: Concretization, 
    id: ProcessIdentity, e: EventInt, include: Boolean)
      : Unit

  /** An iterator over the set. */
  def iterator: Iterator[TransitionTemplateSet.TransitionTemplate]
}

// ==================================================================

/** A very simple (prototype) implementation of TransitionTemplateSet. */
class SimpleTransitionTemplateSet extends TransitionTemplateSet{
  type TransitionTemplate = TransitionTemplateSet.TransitionTemplate

  /** A HashSet containing the transition templates. */
  private val set = new HashSet[TransitionTemplate]()

  /** Add the tuple (pre, post, id, e, include) to the set. */
  def add(pre: Concretization, post: Concretization, 
      id: ProcessIdentity, e: EventInt, include: Boolean) =
    set.add((pre, post, id, e, include))

  /** An iterator over the set. */
  def iterator: Iterator[TransitionTemplate] = 
    set.iterator
}
