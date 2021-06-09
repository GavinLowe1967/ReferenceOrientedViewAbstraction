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

  // Profiler.count("MissingInfo"+missingViews.length)

  assert(missingCommon.length <= 2, 
    "missingCommon.length = "+missingCommon.length)
  assert(missingViews.length <= 7, "missingViews.length = "+missingViews.length)
  // FIXME: not true in general

  private def sort = {
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
      else missingViews(j) = null
    }
    // IMPROVE: remove following
    for(i <- 0 until missingViews.length-1)
      if(missingViews(i) != null && missingViews(i+1) != null)
        assert(missingViews(i).compare(missingViews(i+1)) < 0,
          "\n"+missingViews.map(_.toString).mkString("\n"))
  }

  sort

  /** Number of non-null entries in missingCommon and missingView. */
  private var remainingCount = missingCommon.length+missingViews.length

  /** Has newView been found already? */
  private var newViewFound = false

  /** Record that newView has already been seen, so this is redundant. */
  def markNewViewFound = newViewFound = true

  /** Is this complete? */
  @inline def done = remainingCount == 0 || newViewFound

  import MissingCommon.ViewBuffer

  /** Update the MissingCommon entries in this, based on cv being a possible
    * match to the first clause of the obligation.  Add to ab all Views that
    * this needs to be registered against in the store.  cv is expected to be
    * a possible match to at least one member of missingCommon0. 
    * @return true if this is now complete. */
  def updateMissingCommon(cv: ComponentView, views: ViewSet, ab: ViewBuffer)
      : Boolean = {
    var i = 0
    while(i < missingCommon.length){
      val mc = missingCommon(i)
      if(mc != null && mc.matches(cv))
        if(mc.updateMissingCommon(cv, views, ab)){
          missingCommon(i) = null; remainingCount -= 1
        }
      i += 1
    }
    done
  }

  /** Update the MissingCommon fields of this based upon the addition of cv. cv
    * is expected to match the head of a MissingCommon value.  Return the
    * views against which this should now be registered, or null if all the
    * missingCommon entries are satisfied.  */ 
  def updateMCMissingViews(cv: ComponentView, views: ViewSet): ArrayBuffer[ComponentView] = {
    // Remove cv from each element of missingCommon.
    var i = 0; var ab: ArrayBuffer[ComponentView] = null
    assert(missingCommon.length == 1) // FIXME
    while(i < missingCommon.length){
      val mc = missingCommon(i)
      if(mc != null){
        ab = mc.updateMissingViews(cv, views)
        if(mc.done){ missingCommon(i) = null; remainingCount -= 1 }
      }
      i += 1
    }
    assert(ab != null || missingCommon.forall(_ == null))
    ab
  }

  /** Update this based on the addition of cv.  cv is expected to match a
    * missing view that was added to missingViews (maybe subsequently
    * removed).
    * @return true if its state changes. */
  def updateMissingViews(cv: ComponentView) = {
    // Remove cv from missingViews
    var i = 0 //; var changed = false
    while(i < missingViews.length){
      if(missingViews(i) == cv){ 
        missingViews(i) = null; remainingCount -= 1 // ; changed = true
      }
      i += 1
    }
    // changed
  }
// IMPROVE: maybe EffectOnStore should store MissingInfos separately,
// depending on which of the phases of update1 is relevant.

  /** Check that this contains no element of views remains in missingViews. */
  def sanityCheck(views: ViewSet) = {
    assert(!done)
    for(v <- missingViews; if v != null) assert(!views.contains(v))
    for(mc <- missingCommon) if(mc != null) mc.sanityCheck(views)
  }

  override def toString =
    s"MissingInfo($newView, ${missingViews.mkString("<",",",">")}, "+
      missingCommon.mkString("<",",",">")

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

  /** Equality: same newView, missingViews and missingCommon (up to equality,
    * ignoring nulls. */
  override def equals(that: Any) = that match{ 
    case mi: MissingInfo => 
      mi.newView == newView && equalExceptNull(mi.missingViews, missingViews) &&
      equalExceptNull(mi.missingCommon, missingCommon)
      // val mvLen = missingViews.length; val mcLen = missingCommon.length
      // if(mi.newView == newView && mi.missingViews.length == mvLen &&
      //     mi.missingCommon.length == mcLen){
      //   // Test if missingViews agree
      //   var i = 0
      //   while(i < mvLen && mi.missingViews(i) == missingViews(i)) i += 1
      //   if(i < mvLen) false
      //   else{
      //     // test if missingCommon agree
      //     i = 0
      //     while(i < mcLen && mi.missingCommon(i) == missingCommon(i)) i += 1
      //     i == mcLen
      //   }
      // }
      // else false
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

  def size = 
    missingViews.filter(_ != null).length + 
      missingCommon.filter(_ != null).map(_.size).sum

  def mcCount = missingCommon.length
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
