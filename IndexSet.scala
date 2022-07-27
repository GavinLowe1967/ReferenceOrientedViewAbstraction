package ViewAbstraction

import scala.collection.mutable.{ArrayBuffer}

/** A set of indices into an array of ComponentViews for a particular
  * postServersIndex.  The set contains at least all indices i
  * s.t. !ofOtherTypes(i).containsDoneInducedByIndex(postServersIndex).  It
  * aims not to hold too many others. */
abstract class IndexSet(
  postServersIndex: Int, ofOtherTypes: ArrayBuffer[ComponentView]){

  /** Should index ix be included? */
  @inline protected def include(ix: Int) =
    !ofOtherTypes(ix).containsDoneInducedByIndex(postServersIndex)

  /** Add i to the set.  In the array-based implementation: If purge = true, try
    * purging old values if we need to extend the array. */
  def add(i: Int, purge: Boolean): Unit

  /** An iterator over the set. */
  def iterator: Iterator[Int]
}

// ==================================================================

/** A set of indices into ofOthertypes.  The set contains at least all indices
  * i s.t. !ofOtherTypes(i).containsDoneInducedByIndex(postServersIndex).  It
  * aims not to hold too many others.  This version stores the indices in an
  * array. */
class ArrayIndexSet(
  postServersIndex: Int, ofOtherTypes: ArrayBuffer[ComponentView])
    extends IndexSet(postServersIndex, ofOtherTypes){
  /** The amount of space available for indices. */
  private var spaces = 4

  /** The indices themselves. */
  private var indices = new Array[Int](spaces)

  /** Count of the number of indices held.  The indices are in indices[0..n). */
  private var n = 0

  /** Add i to the set.  If purge = true, try purging old values if we need to
    * extend the array. */
  def add(i: Int, purge: Boolean) = if(include(i)){
    if(n == spaces){
      if(purge){   // Purge old values
        val oldIndices = indices; indices = new Array[Int](spaces)
        var j = 0; n = 0
        while(j < spaces){
          val ix = oldIndices(j); j += 1
          if(include(ix)){ indices(n) = ix; n += 1 }
        }
        //Profiler.count("NewViewSet.purge")
      }
      if(n > 3*spaces/4){ // Also resize.  IMPROVE: think about condition
                          //Profiler.count(s"NewViewSet.resize $purge")
        resizeTo(spaces*2)
      }
    } // end of purging and resizing
    indices(n) = i; n += 1
  }

  /** Resize indices to size newSpaces. */
  @inline private def resizeTo(newSpaces: Int) = {
    val oldSpaces = spaces; spaces = newSpaces
    val oldIndices = indices; indices = new Array[Int](spaces)
    var j = 0
    while(j < n){ indices(j) = oldIndices(j); j += 1 }
  }

  /* We lock this object while there is a current iterator. */

  /** Is this object locked? */
  private var locked = false

  /** Lock this object. */
  private def lock() = synchronized{ while(locked) wait(); locked = true }

  /** Unlock this object. */
  private def unlock() = synchronized{ locked = false; notify() }

  /** Produce an iterator.  No call to add should happen while the iterator is
    * being used.  The implementation ensures that two iterators are not used
    * concurrently. */
  def iterator = { lock(); mkIterator }

  /** Produce an iterator.  No call to add should happen while the iterator is
    * being used.  And two iterators should not be used concurrently. */
  private def mkIterator = new Iterator[Int]{
    /** Index into indices of the next value to return. */
    private var i = 0

    /** The index of the next empty slot in indices.   */
    private var nextFree = 0

    /* While we iterate, we also purge indices that shouldn't be included.  The
     * set currently represents indices[0..nextFree) ++ indices[i..n).
     * The elements of the former segment have been returned.  We still need
     * to return appropriate indices from the latter segment.  NOTE: this
     * isn't thread-safe. */

    /** Advance i to the next value s.t. include(i). */
    private def advance = while(i < n && !include(indices(i))) i += 1
      
    advance

    def hasNext =
      if(i < n) true
      else{ // finished
        n = nextFree // Update n corresponding to purged entries
        if(spaces > 4 && spaces > 2*n){ // downsize
                                        // Profiler.count("NewViewSet.downsize")
          resizeTo(3*n/2 max 4)
        }
        unlock() // release the enclosing object
        false
      }

    def next() = {
      assert(locked) // IMPROVE
      val res = indices(i)
      // Copy this index into the initial segment.  If nextFree = i, this is
      // a no-op.
      indices(nextFree) = res; nextFree += 1; i += 1; advance; res
    }
  } // end of Iterator

} // end of IndexSet

// ==================================================================

/** An implementation of IndexSet using a linked list. */
class LinkedListIndexSet(
  postServersIndex: Int, ofOtherTypes: ArrayBuffer[ComponentView])
    extends IndexSet(postServersIndex, ofOtherTypes){

  /** Nodes from which the linked list is formed. */
  private class Node(val index: Int){
    /** The next node in the list. */
    private var next: Node = null

    /** Get the next node. */
    def getNext = synchronized{ next }

    /** Set the next node to newNext. */
    def setNext(newNext: Node) = synchronized{ next = newNext }

    /** Remove the next node if it is expNext.  Return the new next node. */
    def removeNext(expNext: Node): Node = synchronized{
      if(next == expNext) next.synchronized{
        val nextNext = next.next; next = nextNext; nextNext
      }
      else next
    }
    // Note: we lock nodes in list order, so this doesn't create deadlocks. 
  }

  /** Dummy header for the linked list. */
  private val head = new Node(-1)

  /** Add i to the set.  */
  def add(i: Int, purge: Boolean): Unit = {
    val node = new Node(i); node.setNext(head.getNext); head.setNext(node)  
  }
  // Note: we add at the front, because tracking the last node is tricky.

  /** An iterator over the set. */
  def iterator: Iterator[Int] = new Iterator[Int]{
    /** The previous node in the list. */
    private var prev = head

    /** The next node in the list. */
    private var nextNode = head.getNext

    /** Advance nextNode to one whose index should be included. */
    private def advance() = 
      while(nextNode != null && !include(nextNode.index)){
        // remove nextNode
        nextNode = prev.removeNext(nextNode)
      }
    // Note: if prev has been removed from the list, then the update of
    // prev.next won't actually remove nextNode from the list; however, this
    // is just an optimisation.

    def hasNext = { advance(); nextNode != null }

    def next() = {
      prev = nextNode; nextNode = nextNode.getNext; prev.index
    }

  }
}
