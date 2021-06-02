package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.ArrayBuffer


/** Information capturing when newView might be added to the ViewSet: once all
  * of missingViews0 have been added, and all the obligations represented by
  * missingCommon0 have been satisfied. */
class MissingInfo(
  val newView: ComponentView, missingViews0: List[ComponentView],
  missingCommon0: List[MissingCommon]
){
  /** Lists of component views necessary to satisfy this constraint: all must be
    * added to the ViewSet.  cf. item 1 on page 113 of notebook. */
  private var missingViews: List[ComponentView] = missingViews0

  /** Information about views necessary to satisfy this constraint.  Each
    * represents an obligation to instantiate a component with a particular
    * identity.  cf. item 2 on page 113 of the notebook.  All must be
    * satisfied in order to satisfy this constraint.  */
  private var missingCommon: List[MissingCommon] = missingCommon0
  // It will be unusual for the list to contain more than one element, I think. 
// IMPROVE, all the above share the same servers, cpts1, cpts2

  assert(missingCommon.length <= 1) // FIXME: not true in general

  def done = missingViews.isEmpty && missingCommon.isEmpty

  import MissingCommon.ViewBuffer

  /** Update the MissingCommon entries in this, based on cv being a possible
    * match to the first clause of the obligation.  Add to ab all Views that
    * this needs to be registered against in the store.  cv is expected to be
    * a possible match to at least one member of missingCommon0. 
    * @return true if this is now complete. */
  def updateMissingCommon(cv: ComponentView, views: ViewSet, ab: ViewBuffer)
      : Boolean = {
    // var matched = false // have we found a MissingCommon entry that matches?
    var mcs = missingCommon; missingCommon = List()
    while(mcs.nonEmpty){
      val mc = mcs.head; mcs = mcs.tail
      if(mc.matches(cv)){
        // matched = true
        if(!mc.updateMissingCommon(cv, views, ab)) missingCommon ::= mc
        // else println(s"Removed $mc from $this")
      }
      else missingCommon ::= mc
    }
    // if(debugging && !matched) // check precondition
    //   assert(missingCommon0.exists(mc => mc.matches(cv)),
    //     s"\nupdateMC($cv):\n  $missingCommon\n $missingCommon0")
    done
  }

  /** Update this based on the addition of cv.  cv is expected to match a
    * missing view that was added to missingViews or missingCommon (maybe
    * subsequently removed).
    * @return true if this is now complete. */
  def updateMissingViews(cv: ComponentView): Boolean = {
    // Remove cv from each element of missingCommon.
    var mcs = missingCommon; missingCommon = List()
    while(mcs.nonEmpty){
      val mc = mcs.head; mcs = mcs.tail
      if(! mc.updateMissingViews(cv)) missingCommon ::= mc
    }

    // Remove cv from missingViews
    var mvs = missingViews; missingViews = List()
    while(mvs.nonEmpty){
      val mv = mvs.head; mvs = mvs.tail
      if(mv != cv) missingViews ::= mv
    }

    done
  }
// IMPROVE: maybe EffectOnStore should store MissingInfos separately,
// depending on which of the phases of update1 is relevant.

  /** Check that this contains no element of views remains in missingViews. */
  def sanityCheck(views: ViewSet) = {
    assert(!done)
    for(v <- missingViews) assert(!views.contains(v))
    for(mc <- missingCommon) mc.sanityCheck(views)
  }

  override def toString =
    s"MissingInfo($newView, $missingViews0, $missingCommon0)"

  override def equals(that: Any) = that match{
    case mi: MissingInfo => 
      mi.newView == newView && mi.missingViews == missingViews &&
      mi.missingCommon == missingCommon
  }

  def size = missingViews.length + missingCommon.map(_.size).sum
}
