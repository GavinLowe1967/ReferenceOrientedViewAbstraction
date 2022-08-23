package ViewAbstraction

import scala.collection.mutable.{HashMap,HashSet,ArrayBuffer}
import ox.gavin.profiling.Profiler

/* Note: all classes in this file assume that `add` is not called concurrently
 * with any other operation. */

/** An implementation of ViewSet allowing efficient iteration. */
class NewViewSet extends ViewSet{
  /** A set containing all the views. */
  private val allViews = new MyShardedHashSet[ReducedComponentView]
  // IMPROVE: it would be better to use ComponentView here.  But then we
  // couldn't call contains on it with a ReducedComponentView.  We could
  // implement the set directly, like ComponentsSet.

  /** For each ServerStates, a representation of all views with those
    * servers.   */
  private val serversBased = new ShardedHashMap[ServerStates, ServerBasedViewSet]

  /** For each ServerStates and principal state, all corresponding views.  Each
    * ArrayBuffer is protected by a synchronized block on itself during
    * add. */
  private val serversPrincipalBased = 
    new ShardedHashMap[(ServerStates, State), ArrayBuffer[ComponentView]]

  /** Add sv to this. */
  def add(view: ComponentView) : Boolean = {
    if(allViews.add(view)){
      // add to serversBased
      val sbSet = 
        serversBased.getOrElseUpdate(view.servers, new ServerBasedViewSet)
      sbSet.add(view) // sbSet is thread-safe
      // add to serversPrincipalBased
      val ab = serversPrincipalBased.getOrElseUpdate(
          (view.servers, view.principal), new ArrayBuffer[ComponentView])
      ab.synchronized{ ab += view }
      true
    }
    else false
  }

  /** Does this contain view? */
  def contains(view: ReducedComponentView): Boolean = allViews.contains(view)

  /** Does this contain a view corresponding to servers and cpts? */
  def contains(servers: ServerStates, cpts: Array[State]): Boolean = 
    allViews.contains(new ReducedComponentView(servers, cpts))
  // IMPROVE: the above is potentially inefficiency

  /** Get the view in this corresponding to v.  Pre: there is one. */
  def get(v: ComponentView): ComponentView = {
    // println("NewViewSet.get")
    val ab = serversPrincipalBased((v.servers, v.principal))
    // Search through ab.  This is only done when debugging, so we can put up
    // with the inefficiency.
    var i = 0
    while(i < ab.size && ab(i) != v) i += 1
    assert(i < ab.size, s"NewViewSet.get: not found $v\n$ab")
    ab(i)
  }

  /** The number of elements in the set. */
  def size: Long = allViews.size

  /** Iterator over all views v such that trans might induce a new view from
    * v. */
  override def iterator(trans: Transition): Iterator[ComponentView] = 
    serversBased.get(trans.preServers) match{
      case Some(sbvs) => sbvs.iterator(trans)
      case None => Iterator.empty[ComponentView]
    }

  /** Iterator over all views matching servers. */
  override def iterator(servers: ServerStates) : Iterator[ComponentView] =
    serversBased.get(servers) match{
      case Some(sbvs) => sbvs.iteratorAll
      case None => Iterator.empty[ComponentView]
    }

  /** Iterator over all views matching servers and principal. */
  override def iterator(servers: ServerStates, principal: State)
      : Iterator[ComponentView] = 
    serversPrincipalBased.get((servers, principal)) match{
      case Some(ab) => ab.iterator
      case None => Iterator.empty[ComponentView]
    }

  /** Iterator over all views. */
  def iterator = allViews.iterator.map(_.asInstanceOf[ComponentView])
  // IMPROVE: that's a nasty hack

  override def toString = allViews.toString
}


// ==================================================================

/** A set of views, all of which have the same servers. */
class ServerBasedViewSet{
  import ServerBasedViewSet.{numTypeSets,intToBoolArray}

  /** All the views in this. */
  private val views = new ArrayBuffer[ComponentView]

  /** A set of views for each subset of the types. */
  private val byAcquiredRefTypes = Array.tabulate(numTypeSets)(i => 
    new PrincTypesViewSet(intToBoolArray(i)))

  /** Add */
  def add(view: ComponentView): Unit = synchronized{
    views += view
    var i = 0
    while(i < numTypeSets){ byAcquiredRefTypes(i).add(view); i += 1 }
  }

  def iterator(trans: Transition): Iterator[ComponentView] = {
    if(trans.serverGetsNewId) iteratorAll
    else{
      val index =
        if(singleRef) ServerBasedViewSet.boolArrayToInt(trans.anyAcquiredRefs)
        else 0
      byAcquiredRefTypes(index).iterator(trans)
    }
  }

  @inline def iteratorAll: Iterator[ComponentView] = views.iterator
}

// ==================================================================

object ServerBasedViewSet{
  /** The number of sets of types. */
  private val numTypeSets = if(singleRef) 1<<numTypes else 1

  /** An array of Bools, whose j'th entry is true if the j'th bit of i is 1. */
  @inline private def intToBoolArray(i: Int): Array[Boolean] = 
    Array.tabulate(numTypes)(j => (i&(1 << j)) != 0)
  // IMPROVE: Maybe tabulate these

  /** Convert a to an int, interpreting it as a binary number. */
  @inline private def boolArrayToInt(a: Array[Boolean]): Int = {
    var i = 0; var index = 0; var k = 1 
    // Inv: index is the representation of a[0..i), giving value 2^j for a
    // true in position j; k = 2^i.
    while(i < numTypes){ if(a(i)) index += k; i += 1; k *= 2 }
    assert(intToBoolArray(index).sameElements(a))
    index
  }
}

// ==================================================================

/** A view set corresponding to a particular set of the types corresponding to
  * typeFlags.  Views are treated differently depending on whether the
  * principal is of one of these types.  */
class PrincTypesViewSet(typeFlags: Array[Boolean]){
  /** All views in the set whose principal's type is an element of typeFlags. */
  private val ofTheseTypes = 
    if(singleRef) new ArrayBuffer[ComponentView] else null

  /** All views in the set whose principal's type is not an element of
    * typeFlags. */
  private val ofOtherTypes = new ArrayBuffer[ComponentView]

  /** For each postServers, indices ofOtherTypes corresponding to views v s.t. v
    * might not satisfy containsDoneInduced(postServers).  Indexed by
    * postServers.index.  Values of null or beyond the end of the array
    * correspond to all indices.   */
  private var ofOtherTypesByPostServers = new Array[IndexSet](0) 

  /** All views in ofOtherTypes, indexed by the control states of the
    * components. */
  private val byControlState = 
    new Array[ArrayBuffer[ComponentView]](numCptControlStates)

  /** Get the element of ofOtherTypesByPostServers corresponding to
    * postServersIndex, initialising it if needs be. */
  private def getIndexSet(postServersIndex: Int): IndexSet = synchronized{
    if(postServersIndex >= ofOtherTypesByPostServers.length){ // extend array
      val oldOOTBPS = ofOtherTypesByPostServers; val oldLen = oldOOTBPS.length
      ofOtherTypesByPostServers = new Array[IndexSet](postServersIndex+1)
      var i = 0
      while(i < oldLen){ ofOtherTypesByPostServers(i) = oldOOTBPS(i); i += 1 }
    }
    val ixSet = ofOtherTypesByPostServers(postServersIndex)
    if(ixSet == null){ // Initialise new IndexSet
      val newIxSet = new LinkedListIndexSet(postServersIndex, ofOtherTypes)
      var j = 0
      while(j < ofOtherTypes.length){ newIxSet.add(j, false); j += 1 }
      ofOtherTypesByPostServers(postServersIndex) = newIxSet; newIxSet
    }
    else ixSet
  }

  /** Add view to this set. */
  def add(view: ComponentView) = {
    if(singleRef && typeFlags(view.principal.family))
      ofTheseTypes += view
    else{
      ofOtherTypes += view
      // Add index to ofOtherTypesByPostServers
      val index = ofOtherTypes.length-1; var i = 0
      while(i < ofOtherTypesByPostServers.size){
        // assert(!view.containsDoneInducedByIndex(i)) // IMPROVE
        val ixSet = ofOtherTypesByPostServers(i)
        if(ixSet != null) ixSet.add(index, true)
        i += 1
      }
      // add to byControlState(cs) for each component control state cs
      val cpts = view.components; i = 0
      while(i < cpts.length){
        val cs = cpts(i).cs; i += 1; var j = 0
        // Test if this is the first occurrence of cs
        while(j < i-1 && cpts(j).cs != cs) j += 1
        if(j == i-1){ // First occurrence; add to byControlState(cs)
          if(byControlState(cs) == null)
            byControlState(cs) = new ArrayBuffer[ComponentView]
          byControlState(cs) += view
        }
      }
    }
  }

  /** An iterator over all views s.t. trans might induce a transition to a new
    * view. */
  def iterator(trans: Transition) = new Iterator[ComponentView]{
    /* Unpack relevant parts of trans. */
    private val postServers = trans.post.servers
    private val transChangedServers = trans.changedServers
    private val changingCptCS = trans.changingCptCS
    private val numChangingCpts = changingCptCS.length
    private val postServersIndex = postServers.index

    /* This represents the concatenation of the following:
     * 1. ofThesetypes if singleRef
     * 2. if trans.changedServers, 
     *    ofOtherTypes.filter(v => !v.containsDoneInduced(trans.postServers))
     *    which we implement by iterating over 
     *    ofOtherTypesByPostServers(trans.postServers.index)
     * 3. byControlState(cs) for each cs in trans.changingCptCS (avoiding 
     *    repetitions of views from 2). */

    /** Which of the above three stages are we at? */
    private var stage = if(singleRef) 1 else 2

    /** Index into ofThesetypes at stage 1; index into ofOtherTypes at stage
      * 2; index into trans.changingCptCS at stage 3. */
    private var i = 0

    /** At stage 2, the Indexset to use. */
    val ixSet: Iterator[Int] = 
      if(transChangedServers) getIndexSet(postServersIndex).iterator else null

    /** At stage 3, the views for the next changing component,
      * byControlState(changingCptCS(i)). */
    var ab: ArrayBuffer[ComponentView] = null

    /** Index into ab at stage 3. */
    private var j = 0

    /** Have we produced an induced view with v and postServers? */
    @inline def cdi(v: ComponentView) = 
      v.containsDoneInducedByIndex(postServersIndex)

    /** Advance to reference the next valid view, if appropriate.  */
    @inline private def advance = {
      // Profiler.count(s"advance-$stage")
      // With lazySetNoJoined, 1: 83M, 2: 8M, 3: 63M
      if(stage == 1 && i == ofTheseTypes.length){ 
        if(transChangedServers){ stage = 2; i = 0 }
        else advanceToStage3
      }
      if(stage == 2){ if(!ixSet.hasNext) advanceToStage3  }
      if(stage == 3){
        advance1 // advance within ab
        // If we've reached the end of ab, advance to the next non-empty one
        while(i < numChangingCpts && (ab == null || j == ab.length)){
          i += 1
          if(i < numChangingCpts){ 
            ab = byControlState(changingCptCS(i)); j = 0; advance1 
          }
          // If ab is null or empty, we'll keep advancing
        }
        if(i == numChangingCpts) stage = 4 // done
        //else assert(ab != null && j < ab.length, s"ab = $ab; j = $j")
      }
    }

    /** During stage 3, advance j within ab to the next view v such that
      * !trans.changedServers || v.containsDoneInduced(postServers)).  This is
      * to avoid repetitions of views from stage 2. */
    @inline private def advance1 = if(transChangedServers && ab != null){
      while(j < ab.length && !cdi(ab(j))) j += 1
    }

    /** Advance to stage 3 if non-empty; else stage 4. */
    @inline private def advanceToStage3 = {
      if(numChangingCpts > 0){ 
        stage = 3; i = 0; ab = byControlState(changingCptCS(i)); j = 0
      }
      else stage = 4
    }
    
    // If !singleRef, maybe skip stage 2
    if(!singleRef && !transChangedServers) advanceToStage3

    def hasNext = { advance; stage < 4 }

    /** The next element of the iterator.  Note: this assumes hasNext was called
      * since the previous call of next. */
    def next() = 
      if(stage == 1){ val res = ofTheseTypes(i); i += 1; res }
      else if(stage == 2) ofOtherTypes(ixSet.next())
      else{ assert(stage == 3); val res = ab(j); j += 1; res }
  } // end of Iterator

}

// ==================================================================  
