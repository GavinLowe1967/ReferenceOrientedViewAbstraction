package ViewAbstraction

import scala.collection.mutable.HashSet

/** A set recording the transitions seen so far. */
trait TransitionSet{
  /** Add the transition pre -e-> post. */
  def add(pre: Concretization, e: EventInt, post: Concretization): Unit

  /** An iterator over the transitions. */
  def iterator: Iterator[(Concretization, EventInt, Concretization)]
}


// ==================================================================

/** A very simple (prototype) implementation of TransitionSet. */
class SimpleTransitionSet extends TransitionSet{
  /** A HashSet containing the transitions. */
  private val set = new HashSet[(Concretization, EventInt, Concretization)]()

  /** Add the transition pre -> post. */
  def add(pre: Concretization, e: EventInt, post: Concretization) = 
    set.add((pre, e, post))

  /** An iterator over the transitions. */
  def iterator = set.iterator 
}
 
