package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.ArrayBuffer


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

  assert(missingCommon.length <= 1 && missingViews.length <= 4) 
  // FIXME: not true in general

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

  /** Update this based on the addition of cv.  cv is expected to match a
    * missing view that was added to missingViews or missingCommon (maybe
    * subsequently removed).
    * @return true if this is now complete. */
  def updateMissingViews(cv: ComponentView): Boolean = {
    // Remove cv from each element of missingCommon.
    var i = 0
    while(i < missingCommon.length){
      val mc = missingCommon(i)
      if(mc != null && mc.updateMissingViews(cv)){
        missingCommon(i) = null; remainingCount -= 1
      }
      i += 1
    }
    // Remove cv from missingViews
    i = 0
    while(i < missingViews.length){
      if(missingViews(i) == cv){ missingViews(i) = null; remainingCount -= 1 }
      i += 1
    }
    done
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

  override def equals(that: Any) = that match{ 
    case mi: MissingInfo => 
      val mvLen = missingViews.length; val mcLen = missingCommon.length
      if(mi.newView == newView && mi.missingViews.length == mvLen &&
          mi.missingCommon.length == mcLen){
        var i = 0
        while(i < mvLen && mi.missingViews(i) == missingViews(i)) i += 1
        if(i < mvLen) false
        else{
          i = 0
          while(i < mcLen && mi.missingCommon(i) == missingCommon(i)) i += 1
          i == mcLen
        }
      }
      else false
  }

  def size = 
    missingViews.filter(_ != null).length + 
      missingCommon.filter(_ != null).map(_.size).sum
}
