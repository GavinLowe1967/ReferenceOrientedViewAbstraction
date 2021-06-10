package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet}


/** Information capturing when newView might be added to the ViewSet: once all
  * of missingViews0 have been added, and all the obligations represented by
  * missingCommon0 have been satisfied. */
class MissingInfo(
  val newView: ComponentView, 
  private var missingViews: Array[ComponentView], 
  private var missingCommon: Array[MissingCommon]
){
  /* missingViews contains component views that are necessary to satisfy this
   * constraint: all must be added to the ViewSet.  cf. item 1 on page 113 of
   * notebook.
   * 
   * missingCommon stores information about views necessary to satisfy this
   * constraint.  Each represents an obligation to instantiate a component
   * with a particular identity.  cf. item 2 on page 113 of the notebook.
   * All must be satisfied in order to satisfy this constraint.  
   * 
   * Each is replaced by null when satisfied.  It will be unusual for
   * missingViews to contain more than about four elements, or for
   * missingCommon to contain more than one element.  So we don't compact the
   * arrays.  */

  // We keep missingCommon and missingViews sorted. 
  MissingInfo.sort(missingCommon, missingViews)

  assert(missingCommon.length <= 2, 
    "missingCommon.length = "+missingCommon.length)
  assert(missingViews.length <= 7, "missingViews.length = "+missingViews.length)
  // FIXME: not true in general

  /** Index of the first non-null entry in missingCommon, or
    * missingCommon.length if all are null.  Invariant:
    * missingCommon[0..mcIndex).forall(_ == null). */
  private var mcIndex = 0

  /** Record missingCommon(i) as being completed. */
  @inline private def mcNull(i: Int) = {
    require(missingCommon(i).done)
    missingCommon(i) = null; mcIndex += 1 
  }

  /** Are all the missingCommon entries done? */
  def mcDone = mcIndex == missingCommon.length

  /** Index of first non-null missingView.  Once all MissingCommon are complete,
    * this will be registered against missingViews(mvIndex) in
    * EffectOnStore.store.  */
  private var mvIndex = 0

  /** The first missing view, against which this should be registered once all
    * the MissingCommon are done. */
  def missingHead = missingViews(mvIndex)

  /** Has newView been found already? */
  private var newViewFound = false

  /** Record that newView has already been seen, so this is redundant. */
  def markNewViewFound = newViewFound = true

  /** Is this complete? */
  @inline def done = mcDone && mvIndex == missingViews.length || newViewFound

  import MissingCommon.ViewBuffer

  /** Update the MissingCommon entries in this, based on cv being a possible
    * match to the first clause of the obligation.  Add to ab all Views that
    * this needs to be registered against in the store.  cv is expected to be
    * a possible match to at least one member of missingCommon0. */
  def updateMissingCommon(cv: ComponentView, views: ViewSet, ab: ViewBuffer) = {
// IMPROVE: just the first?
    var i = 0
    while(i < missingCommon.length){
      val mc = missingCommon(i)
      if(mc != null && mc.matches(cv))
        if(mc.updateMissingCommon(cv, views, ab)) mcNull(i)
      i += 1
    }
  }

  /** Update the MissingCommon fields of this based upon the addition of cv. cv
    * is expected to match the head of the missing views of a MissingCommon
    * value. 
// FIXME: assert this
    * Return the views against which this should now be registered, or
    * null if all the missingCommon entries are satisfied.  */ 
  def updateMCMissingViews(cv: ComponentView, views: ViewSet)
      : ArrayBuffer[ComponentView] = {
    var i = 0; var ab: ArrayBuffer[ComponentView] = null
    assert(missingCommon.length == 1) // FIXME
    while(i < missingCommon.length){
      val mc = missingCommon(i)
      if(mc != null){
        ab = mc.updateMissingViews(cv, views)
        if(mc.done) mcNull(i) 
      }
      i += 1
    }
    assert(ab != null || missingCommon.forall(_ == null))
    ab
  }

  /** Update missingViews and mvIndex based upon views.  This is called either
    * when all MissingCommon are first complete, or from missingCommonViewsBy,
    * to advance over subsequent missing views in views.  */
  def updateMissingViews(views: ViewSet) = {
    while(mvIndex < missingViews.length && 
        views.contains(missingViews(mvIndex))){
      missingViews(mvIndex) = null; mvIndex += 1
    }
  }

  /** Update missingViews and mvIndex based on the addition of cv.  cv is
    * expected to match the next missing view. */
  def updateMissingViewsBy(cv: ComponentView, views: ViewSet): Unit = {
    assert(mvIndex < missingViews.length && missingViews(mvIndex) == cv,
      s"mvIndex = $mvIndex, cv = $cv, missingViews = \n"+
        missingViews.mkString("\n"))
    missingViews(mvIndex) = null; mvIndex += 1
    updateMissingViews(views)
  }

  /** Check that: (1) if all the MissingCommon objects are done, then
    * missingViews contains no element of views; (2) otherwise no
    * MissingCommon object has a head missingView in views; (3) if flag, then
    * all MissingCommon objects are done (but not necessarily vice versa). */
  def sanityCheck(views: ViewSet, flag: Boolean) = {
    assert(!done)
    if(flag) assert(mcDone)
    if(mcDone){
      assert(missingCommon.forall(_ == null))
      assert(!views.contains(missingHead), s"$this\nstill contains $missingHead")
    }
    else for(mc <- missingCommon) if(mc != null) mc.sanityCheck(views)
  }

  override def toString =
    s"MissingInfo($newView, ${missingViews.mkString("<",",",">")}, "+
      missingCommon.mkString("<",",",">")

  /** Equality: same newView, missingViews and missingCommon (up to equality,
    * ignoring nulls. */
  override def equals(that: Any) = that match{ 
    case mi: MissingInfo => 
      mi.newView == newView && 
      MissingInfo.equalExceptNull(mi.missingViews, missingViews) &&
      MissingInfo.equalExceptNull(mi.missingCommon, missingCommon)
  }

  private var theHashCode = -1

  /** The hash code for this. */
  override def hashCode = theHashCode

  /** Recalculate the hash code.  This should be performed every time the state
    * of this changes. */
  def rehash() = {
    var h = newView.hashCode; var i = 0
    while(i < missingViews.length){
      if(missingViews(i) != null) h = h*73 + missingViews(i).hashCode
      i += 1
    }
    i = 0
    while(i < missingCommon.length){
      if(missingCommon(i) != null) h = h*73 + missingCommon(i).hashCode
      i += 1
    }
    theHashCode = h
  }

  rehash()

  /** Estimate of the size of this. */
  def size = 
    missingViews.filter(_ != null).length + 
      missingCommon.filter(_ != null).map(_.size).sum

}

// ==================================================================

/** Companion object. */
object MissingInfo{
  /** Sort missingCommon and missingViews. */
  private def sort(
    missingCommon: Array[MissingCommon], missingViews: Array[ComponentView])
  = {
    require(missingCommon.length <= 2)
    // Sort missingCommon
    if(missingCommon.length == 2){
      val cmp = missingCommon(0).compare(missingCommon(1))
      assert(cmp != 0)
      if(cmp > 0){
        val t = missingCommon(0); missingCommon(0) = missingCommon(1);
        missingCommon(1) = t
      }
    }
    // Sort missingViews.  Also replace duplicates by null.  Use insertion
    // sort, as the array is small.
    var i = 1 // Inv: sorted missingViews[0..i)
    while(i < missingViews.length){
      val mv = missingViews(i); var j = i; i += 1
      // Inv missingViews[j+1..i) > mv; missingViews(j) is a duplicate or
      // equals mv, so missingViews[0..j)++missingViews[j+1..i)++[mv] is a
      // permutation of missingViews[0..i) at the start of this iteration.
      while(j > 0 && 
          (missingViews(j-1) == null || mv.compare(missingViews(j-1)) < 0)){
        missingViews(j) = missingViews(j-1); j -= 1
      }
      // Copy mv into position, unless duplicted by missingViews(j-1)
      if(j == 0 || missingViews(j-1) != mv) missingViews(j) = mv
      else missingViews(j) = null // ; remainingCount -= 1 
    }
    // IMPROVE: remove following
    // if(debugging)
    //   for(i <- 0 until missingViews.length-1)
    //     if(missingViews(i) != null && missingViews(i+1) != null)
    //       assert(missingViews(i).compare(missingViews(i+1)) < 0,
    //         "\n"+missingViews.map(_.toString).mkString("\n"))
  }

  /** Do xs and ys hold the same non-null values? */
  @inline private def equalExceptNull[A](xs: Array[A], ys: Array[A]) = {
    var i = 0; var j = 0
    while(i < xs.length && xs(i) == null) i += 1
    while(j < ys.length && ys(j) == null) j += 1
    // Inv: xs[0..i) and ys[0..j) contain same non-null values, and i, j are
    // at end of array or point to non-null values.
    while(i < xs.length && j < ys.length && xs(i) == ys(j)){
      i += 1; j += 1
      while(i < xs.length && xs(i) == null) i += 1
      while(j < ys.length && ys(j) == null) j += 1
    }
    i == xs.length && j == ys.length 
  }
}


// ==================================================================

/** A set of MissingInfo. */
class MissingInfoSet{
  /** We store MissingInfos in a hash set. */
  private val set = new HashSet[MissingInfo]

  /* Each time a MissingInfo's state changes, its hash is updated.  Since each
   * might be in multiple sets, that means it might be in the wrong place in
   * this HashSet.  However, each call to update sorts things out. */

  /** Add missingInfo to this. */
  def add(missingInfo: MissingInfo): Unit = set.add(missingInfo)

  /** For each MissingInfo mi in this: (1) if mi is done or its newView is in
    * views, then remove mi; (2) remove cv from its views; if it is now done,
    * add its newView to result and remove mi from this. */
// IMPROVE comment
  def update(cv: ComponentView, views: ViewSet, 
      result: ArrayBuffer[ComponentView]) 
  = { ???
    // Add nv to result if not already there
    def maybeAdd(nv: ComponentView) = if(!result.contains(nv)) result += nv
    // The new value for the set.
    val newSet = new HashSet[MissingInfo]

    // MissingInfos that need to be removed from this set.
    // var toRemove = List[MissingInfo]()
    // // MissingInfos whose states have changed: they need to be removed,
    // // rehashed and re-added.
    // var changedMIs = List[MissingInfo]()

    // for(mi <- set.iterator; if !mi.done){
    //   if(views.contains(mi.newView)) mi.markNewViewFound
    //   else{
    //     val changed = mi.updateMissingViews(cv) // if changed, re-store
    //     if(mi.done) maybeAdd(mi.newView)
    //     else{ 
    //       if(changed) mi.rehash // IMPROVE: do this in updateMissingViews?
    //       newSet.add(mi)
    //     }
    //   }
    //}

    // for(mi <- toRemove) set.remove(mi)
    // for(mi <- changedMIs){ set.remove(mi); mi.rehash; set.add(mi) }

  }

}
