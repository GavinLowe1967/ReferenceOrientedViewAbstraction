package ViewAbstraction

/** Information about an induced transition.  This corresponds to transition
  * trans = pre -e-> post inducing
  * cv == (pre.servers, oldCpts) -> (post.servers, newCpts) == newView.*/
class InducedTransitionInfo(
  newView: ReducedComponentView, trans: Transition,
  oldCpts: Array[State], cv: ComponentView, newCpts: Array[State]
){
  require(trans.pre.components.length <= 3 && cv.components.length <= 2)
  require(trans.pre.servers == cv.servers)

  @inline def servers = cv.servers

  @inline def preCpts = trans.pre.components

  @inline def cpts = oldCpts

  @inline def prePrincipal = preCpts(0)

  /** Has newView been found already? */
  private var newViewFound = false

  /** Record that newView has already been seen, so this is redundant. */
  def markNewViewFound = synchronized{ newViewFound = true }

  /** Has newView been marked as found? */
  def isNewViewFound = synchronized{ newViewFound }

  /** Does views contain newView?  Store the result. */
  def isNewViewFound(views: ViewSet) = synchronized{
    newViewFound ||
    (if(views.contains(newView)){ newViewFound = true; true } 
    else false)
  }

  /** Get the ComponentView corresponding to this, setting its creation
    * information. */
  def get: ComponentView = {
    val v =  ComponentView.fromReducedComponentView(newView)
    v.setCreationInfoIndirect(trans, oldCpts, cv, newCpts)
    v
  }

  override def toString = {
    s"$trans\n operating on $cv\n induces $cv \n== "+
      s"(${trans.pre.servers}, ${StateArray.show(oldCpts)})\n -> "+
      s"(${trans.post.servers}, ${StateArray.show(newCpts)})\n== $newView"
  }
}

// ==================================================================

import RemappingExtender.CandidatesMap

/** Information about missing cross references.  missingViews contains
  * component views that are necessary to satisfy condition (b) of the induced
  * transition corresponding to inducedTrans: all must be added to the
  * ViewSet. commonMissingPids is the common missing identities for condition
  * (c). */
class MissingCrossReferences(
  val inducedTrans: InducedTransitionInfo,
  missingViews: Array[ReducedComponentView],
  map: RemappingMap, candidates: CandidatesMap,
  val commonMissingPids: Array[ProcessIdentity]
){
  assert(missingViews.nonEmpty && missingViews.forall(_ != null)) 
  // Check sorted
  for(i <- 0 until missingViews.length-1) 
    assert(missingViews(i).compare(missingViews(i+1)) < 0)

  assert(missingViews.length <= 12, "missingViews.length = "+missingViews.length)
  // At most, a reference from each component of pre to each component of cv,
  // and vice versa: 3*2*2.

  @inline def isNewViewFound(views: ViewSet) = inducedTrans.isNewViewFound(views)

  /** Index of the next element of missingViews needed. */
  private var mvIndex = 0

  /** The first missing view, against which this should be registered. */
  def missingHead = synchronized{ missingViews(mvIndex) }

  /** Is this complete? */
  @inline def done = 
    synchronized{ mvIndex == missingViews.length || inducedTrans.isNewViewFound }

  /** Update missingViews and mvIndex based on the addition of cv.  cv is
    * expected to match the next missing view. */
  def updateMissingViewsBy(cv: ComponentView, views: ViewSet) = synchronized{
    // Is following TOCTTOU? 
    require(mvIndex < missingViews.length && missingViews(mvIndex) == cv,
      s"mvIndex = $mvIndex, cv = $cv, missingViews = \n"+
        missingViews.mkString("\n"))
    mvIndex += 1
    while(mvIndex < missingViews.length && 
      (missingViews(mvIndex) == null || views.contains(missingViews(mvIndex)))
    )
      mvIndex += 1
  }


}

// =======================================================

object MissingCrossReferences{
  /** Sort missingViews, removing duplicates. */
  def sort(missingViews: Array[ReducedComponentView])
      : Array[ReducedComponentView] = {
    // Use insertion sort, as the array is small.
    var i = 1 // Inv: sorted missingViews[0..i)
    while(i < missingViews.length){
      val mv = missingViews(i); var j = i; i += 1; assert(mv != null)
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
    // IMPROVE following
    missingViews.filter(_ != null)
  }
}
