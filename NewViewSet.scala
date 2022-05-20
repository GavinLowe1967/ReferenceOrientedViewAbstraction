package ViewAbstraction

import scala.collection.mutable.{HashMap,HashSet,ArrayBuffer}
import ox.gavin.profiling.Profiler

/** An implementation of ViewSet allowing efficient iteration. */
class NewViewSet extends ViewSet{
  println("NewViewSet")
  assert(singleRef) // For the moment IMPROVE
  /** A set containing all the views. */
  private val allViews = new HashSet[ReducedComponentView]
  // IMPROVE: it would be better to use ComponentView here.  But then we
  // couldn't call contains on it with a ReducedComponentView.  We could
  // implement the set directly, like ComponentsSet.

  /** For each ServerStates, a representation of all views with those
    * servers. */
  private val serversBased = new HashMap[ServerStates, ServerBasedViewSet]

  /** For each ServerStates and principal state, all corresponding views. */
  private val serversPrincipalBased = 
    new HashMap[(ServerStates, State), ArrayBuffer[ComponentView]]

  /** Add sv to this. */
  def add(view: ComponentView) : Boolean = {
    if(allViews.add(view)){
      // add to serversBased
      val sbSet =
        serversBased.getOrElseUpdate(view.servers, new ServerBasedViewSet)
      sbSet.add(view)
      // add to serversPrincipalBased
      val ab = serversPrincipalBased.getOrElseUpdate(
        (view.servers, view.principal), new ArrayBuffer[ComponentView])
      ab += view
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
    println("NewViewSet.get")
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
  def add(view: ComponentView): Unit = {
    views += view
    var i = 0
    while(i < numTypeSets){ byAcquiredRefTypes(i).add(view); i += 1 }
  }

  def iterator(trans: Transition): Iterator[ComponentView] = {
    // Build index into byAcquiredRefs corresponding to the acquired
    // references in trans.  Inv: index is the representation of
    // trans.anyAcquiredRefs[0..i), giving value 2^j for a true in position j;
    // k = 2^i.
    var i = 0; var index = 0; var k = 1
    while(i < numTypes){
      if(trans.anyAcquiredRefs(i)) index += k
      i += 1; k *= 2
    }
    assert(intToBoolArray(index).sameElements(trans.anyAcquiredRefs))//IMPROVE
    byAcquiredRefTypes(index).iterator(trans)
    // IMPROVE
    //views.iterator
  }

  def iteratorAll: Iterator[ComponentView] = views.iterator
}

// ==================================================================

object ServerBasedViewSet{
  /** The number of sets of types. */
  private val numTypeSets = 1<<numTypes

  /** An array of Bools, whose j'th entry is true if the j'th bit of i is 1. */
  @inline private def intToBoolArray(i: Int): Array[Boolean] = 
    Array.tabulate(numTypes)(j => (i&(1 << j)) != 0)

  // Maybe tabulate these
  // val intToBoolArrayX: Array[Array[Boolean]] = 
  //   Array.tabulate(1 << numTypes)(i => intToBoolArray(i))

}

// ==================================================================

/** A view set corresponding to a particular set of the types corresponding to
  * typeFlags.  Views are treated differently depending on whether the
  * principal is of one of these types.  */
class PrincTypesViewSet(typeFlags: Array[Boolean]){
  /** All views in the set whose principal's type is an element of typeFlags. */
  private val ofTheseTypes = new ArrayBuffer[ComponentView]

  /** All views in the set whose principal's type is not an element of
    * typeFlags. */
  private val ofOtherTypes = new ArrayBuffer[ComponentView]

  /** For each postServers, indices ofOtherTypes corresponding to views v s.t. v
    * might not satisfy containsDoneInduced(postServers).  Indexed by
    * postServers.index.  Values of null or beyond the end of the array
    * correspond to all indices. */
  private var ofOtherTypesByPostServers = new Array[IndexSet](0) 

  /** All views in ofOtherTypes, indexed by the control states of the
    * components. */
  private val byControlState = 
    new Array[ArrayBuffer[ComponentView]](numCptControlStates)

  /** Add view to this set. */
  def add(view: ComponentView) = {
    if(typeFlags(view.principal.family))
      ofTheseTypes += view
    else{
      ofOtherTypes += view
      // Add to ofOtherTypesByPostServers
      var i = 0
      while(i < ofOtherTypesByPostServers.size){
        assert(!view.containsDoneInducedByIndex(i))
        val ixSet = ofOtherTypesByPostServers(i)
        if(ixSet != null /* && !view.containsDoneInducedByIndex(i)*/)
          ixSet.add(i)
        i += 1
      }
      // add to byControlState(cs) for each component control state cs
      val cpts = view.components; i = 0
      while(i < cpts.length){
        val cs = cpts(i).cs; i += 1
        // IMPROVE: only if this is the first occurrence of cs
        // add to byControlState(cs)
        if(byControlState(cs) == null)
          byControlState(cs) = new ArrayBuffer[ComponentView]
        byControlState(cs) += view
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
     * 1. ofThesetypes
     * 2. if trans.changedServers, 
     *    ofOtherTypes.filter(v => !v.containsDoneInduced(trans.postServers))
     * 3. byControlState(cs) for each cs in trans.changingCptCS (avoiding 
     *    repetitions of views from 2). */

    /** Which of the above three stages are we at? */
    private var stage = 1

    /** Index into ofThesetypes at stage 1; index into ofOtherTypes at stage
      * 2; index into trans.changingCptCS at stage 3. */
    private var i = 0

    /** At stage 3, the views for the next changing component,
      * byControlState(changingCptCS(i)). */
    var ab: ArrayBuffer[ComponentView] = null

    /** Index into ab at stage 3. */
    private var j = 0

    /** Have we produced an induced view with v and postServers? */
    @inline def cdi(v: ComponentView) = {
      val res = v.containsDoneInducedByIndex(postServersIndex)
      // Profiler.count(s"NewViewSet.cdi: $res")
      // With lazySetNoJoined, ~80B, 8M false
      res
    }

    /** Advance to reference the next valid view, if appropriate.  */
    @inline private def advance = {
      // Profiler.count(s"advance-$stage")
      // With lazySetNoJoined, 1: 83M, 2: 8M, 3: 63M
      if(stage == 1 && i == ofTheseTypes.length){ 
        if(transChangedServers){ stage = 2; i = 0 }
        else advanceToStage3
      }
      if(stage == 2){
        // skip views v s.t. v.containsDoneInduced(postServers)
        while(i < ofOtherTypes.length && cdi(ofOtherTypes(i))) i += 1
        if(i == ofOtherTypes.length) advanceToStage3
      }
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

// IMPROVE: inline following

    /** During stage 3, advance j within ab to the next view v such that
      * !trans.changedServers || v.containsDoneInduced(postServers)).  This is
      * to avoid repetitions of views from stage 2. */
    @noinline private def advance1 = if(transChangedServers && ab != null){
      while(j < ab.length && !cdi(ab(j))) j += 1
    }

    /** Advance to stage 3 if non-empty; else stage 4. */
    @noinline private def advanceToStage3 = {
      if(numChangingCpts > 0){ 
        stage = 3; i = 0; ab = byControlState(changingCptCS(i)); j = 0
      }
      else stage = 4
    }
    
    def hasNext = { advance; stage < 4 }

    /** The next element of the iterator.  Note: this assumes hasNext was called
      * since the previous call of next. */
    def next() = 
      if(stage == 1){ val res = ofTheseTypes(i); i += 1; res }
      else if(stage == 2){
        val res = ofOtherTypes(i); i += 1; 
        //assert(transChangedServers && !cdi(res)) // IMPROVE
        res
      }
      else{
        assert(stage == 3); val res = ab(j); j += 1; 
        //assert(!transChangedServers || cdi(res)) // IMPROVE
        res
      }
  } // end of Iterator

  /** A set of indices into ofOthertypes.  The set contains at least all indices
    * i s.t. !ofOtherTypes(i).containsDoneInducedByIndex(postServersIndex).
    * It aims not to hold too many others. */
  class IndexSet(postServersIndex: Int){
    /** The amount of space available for indices. */
    var spaces = 4

    /** The indices themselves. */
    var indices = new Array[Int](spaces)

    /** Count of the number of indices held.  The indices are in
      * indices[0..n). */
    var n = 0

    /** Should index ix be included? */
    @inline private def include(ix: Int) =
      !ofOtherTypes(ix).containsDoneInducedByIndex(postServersIndex)

    /** Add i to the set. */
    def add(i: Int) = if(include(i)){
      if(n == spaces){   
        // Purge old values
        val oldIndices = indices; indices = new Array[Int](spaces)
        var j = 0; n = 0
        while(j < spaces){
          val ix = oldIndices(j); j += 1
          if(include(ix)){ indices(n) = ix; n += 1 }
        }
        Profiler.count("NewViewSet.purge")
        if(n > spaces/2){ // Also resize
          Profiler.count("NewViewSet.resize")
          val oldSpaces = spaces; spaces = spaces*2
          val oldIndices = indices; indices = new Array[Int](spaces)
          var j = 0
          while(j < n){ indices(j) = oldIndices(j); j += 1 }
        }
      } // end of purging and resizing
      indices(n) = i; n += 1
    }

    /** Produce an iterator.  No call to add should happen while the iterator is
      * being used.  And two iterators should not be used concurrently. */
    def iterator = new Iterator[Int]{
      /** Index into indices of the next value to return. */
      var i = 0

      /** The index of the next empty slot in indices.   */
      var nextFree = 0

      /* While we iterate, we also purge indices that shouldn't be included.  The
       * set currently represents indices[0..nextFree) ++ indices[i..n).
       * The elements of the former segment have been returned.  We still need
       * to return appropriate indices from the latter segment.  NOTE: this
       * isn't thread-safe. */

      /** Advance i to the next value s.t. include(i). */
      private def advance = while(i < n && !include(i)) i += 1
      
      advance

      def hasNext = 
        if(i < n) true 
        else{ n = nextFree; false } // Update n corresponding to purged entries

      def next() = { 
        val res = indices(i)
        // Copy this index into the initial segment.  If nextFree = i, this is
        // a no-op.
        indices(nextFree) = res; nextFree += 1
        i += 1; advance; res
      }
    }

  } // end of IndexSet

}
