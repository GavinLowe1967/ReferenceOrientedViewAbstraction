package ViewAbstraction

import scala.collection.mutable.HashSet

class NewTransitionSet{
  private var underlying = new HashSet[Transition]


  /** Add the transition t. */
  def add(t: Transition): Boolean = {
    if(underlying.add(t)){
      ???
      true
    }
    else false
  }

  /** An iterator over the transitions, producing transitions that might produce
    * sufficient unifications with cv to give at least one induced
    * transition. */
  def iterator(cv: ComponentView): Iterator[Transition] = ???

  def size: Long = underlying.size

  def contains(trans: Transition): Boolean = underlying.contains(trans)
}

