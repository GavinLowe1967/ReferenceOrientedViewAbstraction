package ViewAbstraction

import scala.collection.mutable.HashSet

/** A set recording the transitions seen so far. */
trait TransitionSet{
  /** Add the transition pre -> post. */
  def add(pre: Concretization, post: Concretization): Unit

  /** An iterator over the transitions. */
  def iterator: Iterator[(Concretization, Concretization)]
}


// ==================================================================

/** A very simple (prototype) implementation of TransitionSet. */
class SimpleTransitionSet extends TransitionSet{
  /** A HashSet containing the transitions. */
  private val set = new HashSet[(Concretization, Concretization)]()

  /** Add the transition pre -> post. */
  def add(pre: Concretization, post: Concretization) = 
    set.add((pre, post))

  /** An iterator over the transitions. */
  def iterator = set.iterator 
}
 
