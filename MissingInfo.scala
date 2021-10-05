package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet}


/** Information capturing when newView might be added to the ViewSet: once all
  * of missingViews have been added, and all the obligations represented by
  * missingCommon have been satisfied. */
class MissingInfo(
  val newView: ComponentView, 
  private var missingViews: Array[ComponentView], 
  private var missingCommon: Array[MissingCommon]
){
  /* missingViews contains component views that are necessary to satisfy this
   * constraint: all must be added to the ViewSet.  This corresponds to
   * condition (b) in the definition of induced transitions with restricted
   * views.
   * 
   * missingCommon stores information about views necessary to satisfy this
   * constraint.  Each represents an obligation to instantiate a component
   * with a particular identity.  This corresponds to condition (c) in the
   * definition of induced transitions with restricted views.  All must be
   * satisfied in order to satisfy this constraint.
   * 
   * Note: MissingCommon values might be shared between MissingInfo objects.
   * 
   * Each is replaced by null when satisfied.  It will be unusual for
   * missingViews to contain more than about four elements, or for
   * missingCommon to contain more than one element.  So we don't compact the
   * arrays.  */

  /* Overview of main functions.
   * updateMissingCommon     (called from EffectOnStore)
   * |--(MissingCommon.)updateMissingCommon
   * |--advanceMC
   *    |--(MissingCommon.)updateMissingViews
   * 
   * updateMissingViewsOfMissingCommon    (called from EffectOnStore)
   * |--(MissingCommon.)updateMissingViewsBy
   * |--advanceMC
   * 
   * updateMissingViews     (called from EffectOnStore)
   * 
   * updateMissingViewsBy    (called from EffectOnStore)
   * |--updateMissingViews
   */

  require(missingCommon.forall(!_.done))
  require(missingViews.forall(_ != null))

  // We keep missingCommon and missingViews sorted. 
  MissingInfo.sort(missingCommon, missingViews)

  /* missingViews may contain null values: duplicates are replaced by null in
   * the above sort. */

  import MissingCommon.ViewBuffer // ArrayBuffer[ComponentView]

  assert(missingCommon.length <= 2, 
    "missingCommon.length = "+missingCommon.length)
  assert(missingViews.length <= 9, "missingViews.length = "+missingViews.length)
  // FIXME: latter not true in general

  /* Initially we try to discharge the obligations represented by missingCommon.
   * mcIndex represents the next MissingCommon to consider; mcDone gives true
   * when all are satisfied.  Subsequently, the obligations represented by
   * missingViews are considered.   */

  /** Index of the first non-null entry in missingCommon, or
    * missingCommon.length if all are null.  Invariant:
    * missingCommon[0..mcIndex).forall(_ == null). */
  private var mcIndex = 0

  /** Record missingCommon(i) as being completed. */
  @inline private def mcNull(i: Int) = {
    require(missingCommon(i).done); missingCommon(i) = null 
  }

  /** Advance to the next MissingCommon value (if any).  
    * @return a ViewBuffer containing views against which this should now be 
    * registered, or null if all MissingCommon are done. */
  @inline private 
  def advanceMC(views: ViewSet): ViewBuffer = {
    require(missingCommon(mcIndex) == null)
    mcIndex += 1
    if(mcIndex < missingCommon.length){ // consider next 
      assert(mcIndex == 1 && missingCommon.length == 2)
      val mc = missingCommon(mcIndex)
      if(mc == null){ mcIndex += 1; rehashMC(); null } // this one is also done
      else{
        val vb = mc.updateMissingViews(views)
        if(mc.done){  // and now this is done
          mcNull(mcIndex); mcIndex += 1; rehashMC(); null 
        }
        else{ rehashMC(); vb }
      }
    }
    else{ rehashMC(); null }
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

  /** Update the MissingCommon entries in this, based on cv being a possible
    * match to the first clause of the obligation.  cv is expected to be a
    * possible match to the next element of missingCommon.
    * @return a ViewBuffer containing all views that this needs to be registered
    * against in the store if not all MissingCommon are done. */
  def updateMissingCommon(cv: ComponentView, views: ViewSet): ViewBuffer = {
    val mc = missingCommon(mcIndex); assert(mc != null && mc.matches(cv))
    val vb = new ViewBuffer
    mc.updateWithNewMatch(cv, views, vb)
    if(mc.done){
      // Advance to the next MissingCommon (if any), and return views to
      // register against
      mcNull(mcIndex); advanceMC(views)
    }
    else vb
  }

  /** Update the MissingCommon fields of this based upon the addition of cv.
    * Normally, cv will match a missingHead of the next MissingCommon, but not
    * if we've subsequently advanced within the MissingCommons. (IMPROVE:
    * assert this.)
    * @return the views against which this should now be registered, or
    * null if all the missingCommon entries are satisfied.  */ 
  def updateMissingViewsOfMissingCommon(cv: ComponentView, views: ViewSet)
      : ViewBuffer = {
    val mc = missingCommon(mcIndex)
    val vb: ViewBuffer = mc.updateMissingViewsBy(cv, views)
    if(mc.done){ mcNull(mcIndex); advanceMC(views) }
    else vb
  }

  /** Update missingViews and mvIndex based upon views.  This is called either
    * when all MissingCommon are first complete, or from missingCommonViewsBy,
    * to advance over subsequent missing views in views.  */
  def updateMissingViews(views: ViewSet) = {
    require(mcDone)
    while(mvIndex < missingViews.length && 
      (missingViews(mvIndex) == null || views.contains(missingViews(mvIndex)))){
      missingViews(mvIndex) = null; mvIndex += 1
    }
    rehashMV()
  }

  /** Update missingViews and mvIndex based on the addition of cv.  cv is
    * expected to match the next missing view. */
  def updateMissingViewsBy(cv: ComponentView, views: ViewSet): Unit = {
    require(mcDone && mvIndex < missingViews.length && 
      missingViews(mvIndex) == cv,
      s"mvIndex = $mvIndex, cv = $cv, missingViews = \n"+
        missingViews.mkString("\n"))
    missingViews(mvIndex) = null; mvIndex += 1
    updateMissingViews(views)
  }

  /** Check that we have nulled-out all done MissingCommons. */
  def sanity1 = missingCommon.forall(mc => mc == null || !mc.done)

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
    s"MissingInfo(newView = $newView,\n"+
      s"missingViews = ${missingViews.mkString("<",",",">")},\n"+
      "missingCommon = "+missingCommon.mkString("<",",",">")+")"

  /** Equality: same newView, missingViews and missingCommon (up to equality,
    * ignoring nulls. */
  override def equals(that: Any) = that match{ 
    case mi: MissingInfo => 
      mi.newView == newView && 
      MissingInfo.equalExceptNull(mi.missingViews, missingViews) &&
      MissingInfo.equalExceptNull(mi.missingCommon, missingCommon)
  }

  /** The hash code for this. */
  override def hashCode = mcHash ^ mvHash

  /** Hash of newView and missingCommon. */
  private var mcHash = -1

  /** Update mcHash.  Should be called at each update of mcIndex. */
  private def rehashMC() = {
    var h = newView.hashCode; var i = mcIndex
    while(i < missingCommon.length){
      if(missingCommon(i) != null){ // not if we blanked one out when sorting
        h = h*73 + missingCommon(i).hashCode
      }
      i += 1
    }
    mcHash = h
  }

  /** Hash of missingViews. */
  private var mvHash = -1

  /** Update mvHash.  Should be called at each update of mvIndex. */
  private def rehashMV() = {
    var h = 0; var i = mvIndex
    while(i < missingViews.length){
      if(missingViews(i) != null) h = h*73 + missingViews(i).hashCode
      i += 1
    }
  }

  rehashMC(); rehashMV()

  /** Estimate of the size of this. 
    * @return a pair: the number of views in missingViews; and the number of 
    * views in missingCommon. */
  def size: (Int, Int) = 
    (missingViews.count(_ != null),
      missingCommon.filter(_ != null).map(_.size).sum)
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
      if(cmp > 0){
        val t = missingCommon(0); missingCommon(0) = missingCommon(1);
        missingCommon(1) = t
      }
      else if(cmp == 0) // happens on step 46 of lazySet.csp, after ~100K views
        missingCommon(1) = null
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

