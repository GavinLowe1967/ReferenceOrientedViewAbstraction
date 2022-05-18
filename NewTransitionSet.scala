package ViewAbstraction

import scala.collection.mutable.{HashMap,HashSet,ArrayBuffer}

/* We include various bits of jiggery-pokery in these classes, to support
 * efficient iteration. */

/** A set recording the transitions seen so far. */
class NewTransitionSet{
  /** All the transitions added. */
  private var underlying = new HashSet[Transition]

  /** The transitions, partitioned according to their preServers value. */
  private val byPreServers = new HashMap[ServerStates, ServersTransitionSet]
  // Improve: use array indexed by ServerStates?

  /** Add the transition t. */
  def add(t: Transition): Boolean = {
    if(underlying.add(t)){
      val preServers = t.preServers
      byPreServers.get(preServers) match{
        case Some(ts) => /*ts += t*/ ts.add(t)
        case None => 
          val ts = new ServersTransitionSet(preServers);  ts.add(t)
          byPreServers += preServers -> ts
      }
      true
    }
    else{ assert(false); false }
  }

  /** An iterator over the transitions, producing transitions that might produce
    * sufficient unifications with cv to give at least one induced
    * transition. */
  def iterator(cv: ComponentView): Iterator[Transition] = 
    // We need cv.servers = t.pre.servers
    byPreServers.get(cv.servers) match{
      case Some(ts) => ts.iterator(cv)
      case None => Iterator.empty[Transition] 
    }

  /** The number of transitions stored. */
  def size: Long = underlying.size

  /** Does this set contain trans? */
  def contains(trans: Transition): Boolean = underlying.contains(trans)
}

// ==================================================================

/** A set of transitions corresponding to pre.servers = preServers. */
class ServersTransitionSet(preServers: ServerStates){
  /** For each family f, those transitions(t) such that singleRef &&
    * t.anyAcquiredRefs(f) || t.serverGetsNewId.  Each entry is initialised
    * lazily. */
  private val acquiringTrans = new Array[ArrayBuffer[Transition]](numTypes)
  //  Array.fill(numTypes)(new ArrayBuffer[Transition])

  // IMPROVE: maybe transitions s.t. t.serverGetsNewId shouldn't be stored in
  // all entries of acquiringTrans.

  /** For each family f, the transitions not in acquiringTransitions(f),
    * partitioned according to their post.servers value.  Each entry is
    * initialised lazily. */
  private val byPostServers = 
    new Array[HashMap[ServerStates, ServersServersTransitionSet]](numTypes)
    //Array.fill(numTypes)(new HashMap[ServerStates,ServersServersTransitionSet])

  /* For each f, acquiringTrans(f) U U { ssts | (_,ssts) <- byPostServers(f) }
   * gives the same value, and that is the abstract value of this set.  */

  /** Add the transition t. */
  def add(t: Transition) = {
    //all += t
    var f = 0
    while(f < numTypes){
      if(singleRef && t.anyAcquiredRefs(f) || t.serverGetsNewId){
        if(acquiringTrans(f) == null) 
          acquiringTrans(f) = new ArrayBuffer[Transition]
        acquiringTrans(f) += t
      }
      else{
        if(byPostServers(f) == null) byPostServers(f) = 
          new HashMap[ServerStates, ServersServersTransitionSet]
        byPostServers(f).get(t.post.servers) match{
          case Some(ts) => ts.add(t)
          case None =>
            val ts = new ServersServersTransitionSet; ts.add(t)
            byPostServers(f) += t.post.servers -> ts
        }
      } // end of else
      f += 1
    }
  }

  def iterator(cv: ComponentView) = new Iterator[Transition]{
    private val princFamily = cv.principal.family

    /* This iterator can be thought of as the concatenation of (1)
     * acquiringTrans(princFamily).iterator, and (2) an iterator for each
     * element of byPostServers(princFamily): for each postServers, we include
     * all elements if the servers change &&
     * !cv.containsDoneInduced(postServers); otherwise we include just those
     * where a component that changes state matches a control state of cv. */

    /** The current iterator to use. */
    private var thisIterator = {
      val ab = acquiringTrans(princFamily)
      if(ab != null) ab.iterator else null
    }

    /* Invariant: if !thisIterator.hasNext, then we've reached the end of this
     * iterator.  */

    /** Iterator over byPostServers(princFamily). */
    private val byPostServersIterator
        : Iterator[(ServerStates, ServersServersTransitionSet)] = {
      val hm = byPostServers(princFamily)
      if(hm != null) hm.iterator else Iterator.empty
    }

    /** Replace thisIterator if it's finished. */
    private def advance: Unit = 
      while((thisIterator == null || !thisIterator.hasNext) &&
          byPostServersIterator.hasNext){
        val (postServers, ssts) = byPostServersIterator.next()
        if(preServers != postServers && !cv.containsDoneInduced(postServers))
          thisIterator = ssts.iteratorAll
        else thisIterator = ssts.iteratorPossibleUnifs(cv)
      }
    // If !thisIterator.hasNext && !byPostServersIterator.hasNext then we're
    // done.

    advance

    def hasNext = thisIterator.hasNext 

    def next() = { val res = thisIterator.next(); advance; res }
  }
}

// ==================================================================

/** A set of transitions corresponding to a particular choice of pre.servers
  * and post.servers. */
class ServersServersTransitionSet{

  /** All the transitions in this set. */
  private val allTrans = new ArrayBuffer[Transition]

  /** byChangedState(cs) stores those transitions that have a component
    * initially in control state cs that changes state. */
  private val byChangedState = 
    new Array[ArrayBuffer[Transition]](numCptControlStates)

  /** Add the transition t. */
  def add(t: Transition) = { 
    allTrans += t
    // If a component changes state, store in the relevant entry of
    // byChangedState.
    var i = 0; val cpts = t.pre.components
    while(i < cpts.length){
      if(t.changedStateBitMap(i)){
        val cs = cpts(i).cs
        if(byChangedState(cs) == null) 
          byChangedState(cs) = new ArrayBuffer[Transition]
        byChangedState(cs) += t
      }
      i += 1
    }
  }

  /** An iterator over all the transitions in this. */
  def iteratorAll: Iterator[Transition] = allTrans.iterator

  /** An iterator over the transitions such that a component that changes state
    * has the same control state as a component of cv. */
  def iteratorPossibleUnifs(cv: ComponentView) = new Iterator[Transition]{
    /* This is the concatenation of byChangedState(cs) where cs ranges over the
     * distinct control states of cv. */

    /** Index of the next component of cv. */
    private var i = 0

    private val len = cv.components.length

    /** Get the iterator corresponding to component i of cv, if this is the first
      * component with that control state; returns null otherwise, or in lieu
      * of an empty iterator. */
    @inline private def getIterator: Iterator[Transition] = {
      val cs = cv.components(i).cs
      if(isFirstInstanceOfCS(cs)){
        val ab = byChangedState(cs)
        if(ab != null) ab.iterator else null
      }
      else null
    }

    /** Is component i of cv the first component with control state cs? */ 
    @inline private def isFirstInstanceOfCS(cs: ControlState) = {
      var j = 0
      while(j < i && cv.components(j).cs != cs) j += 1
      j == i
    }

    /** The current iterator, corresponding to the control state of
      * cv.components(i). */
    private var thisIter: Iterator[Transition] = getIterator

    /** Advance thisIter to an iterator with elements, if possible. */
    private def advance = 
      while(i < len && (thisIter == null || !thisIter.hasNext)){
        i += 1
        if(i < len) thisIter = getIterator
      }

    advance

    def hasNext = i < len

    def next() = { val res = thisIter.next(); advance; res }
  } // end of iterator

}
