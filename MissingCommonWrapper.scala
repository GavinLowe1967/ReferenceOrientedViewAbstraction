package ViewAbstraction

import scala.collection.mutable.ArrayBuffer
import RemapperP.Remapper

class MissingCommonWrapper(
  val inducedTrans: InducedTransitionInfo,
  commonMissingPids: Array[ProcessIdentity]
// IMPROVE: set commonMissingPids = null if empty
){
  require(inducedTrans.cpts != null)

  def servers = inducedTrans.servers

  def prePrincipal = inducedTrans.prePrincipal

  @inline def isNewViewFound(views: ViewSet) = inducedTrans.isNewViewFound(views)

  /** Index into commonMissingPids. */
  private var pidsIndex = 0

  import MissingCommonWrapper.{Cpts,CptsBuffer}
  // Array[State], Iterable[Cpts], resp

  /** The current MissingCommon.  Corresponds to
    * commonMissingPids(pidsIndex). */
  private var mc: MissingCommon = null

  def missingHeads: Array[ReducedComponentView] = 
    mc.missingHeads.map(cpts => ReducedComponentView(servers, cpts))

  def done = mc == null

  // /** Result returned by operations that update this: the components against
  //   * which this should be registered. */
  // type CptsBuffer = Iterable[Cpts]

  /** Update the missingCandidates of the current MissingCommon based on views.
    * Remove elements of views from the front of each.  If any is now empty,
    * then the MissingCommon is satisfied.  Return views against which this
    * should now be registered, or null if done. */
  def updateMissingViews(views: ViewSet): CptsBuffer = synchronized{
    val buff = mc.updateMissingViews(views)
    if(buff == null) advance1(views) else buff
  }

  /** Update the current MissingCommon based on using cv to instantiate servers
    * || princ1 || c.
    * @return a CptsBuffer containing those Views against which this needs to
    * be registered, namely missingHeads; or null if this is now done. */
  def updateWithNewMatch(cv: ComponentView, views: ViewSet)
      : CptsBuffer = synchronized{
    require(!done)
    val buff = mc.updateWithNewMatch(cv, views)
    if(buff == null) advance1(views) else buff
  }

  /** Advance to the next common missing identity, and initialise the
    * corresponding CommonMissing.  Return the views against which this should
    * now be registered, or null if this is now done. */
  @inline private def advance1(views: ViewSet): CptsBuffer = {
    require(mc.done); pidsIndex += 1; advance(views)
    if(mc != null) mc.missingHeads else null 
  }

  /** Initialise the MissingCommon for the next common missing process identity,
    * if any.  If all are done, set mc = null.  */
  @inline private def advance(views: ViewSet) = {
    var done = false 
    // done = true if we've created an new MissingCommon
    while(pidsIndex < commonMissingPids.length && !done){
      val pid = commonMissingPids(pidsIndex)
      val newMC = MissingCommon.makeMissingCommon(
        inducedTrans.servers, inducedTrans.preCpts, inducedTrans.cpts, 
        pid, views)
      if(newMC == null) pidsIndex += 1 else{ mc = newMC; done = true }
    }
    if(!done) mc = null
  }

  /** Initialise this based on views. */
  def init(views: ViewSet) = advance(views)

}

// ==================================================================

object MissingCommonWrapper{

  type Cpts = Array[State]

  /** Result returned by operations that update a MissingCommonWrapper: the
    * components against which it should be registered. */
  type CptsBuffer = Iterable[Cpts]

  /** Produce a MissingCommonWrapper corresponding to inducedTrans and
    * commonMissingPids; if all required views are in `views` then return
    * null. */
  def apply(inducedTrans: InducedTransitionInfo, 
    commonMissingPids: Array[ProcessIdentity], views: ViewSet)
      : MissingCommonWrapper = {
    val mcw = new MissingCommonWrapper(inducedTrans, commonMissingPids)
    val missingHeads = mcw.init(views)
    if(mcw.done) null else mcw
  }

  import SingleRefEffectOnUnification.commonMissingRefs

  /** Produce a MissingCommonWrapper corresponding to renaming the base view in
    * inducedTrans by map; if all required views are in `views` then return
    * null. */
  def fromMap(
    map: RemappingMap, inducedTrans: InducedTransitionInfo, views: ViewSet)
      : MissingCommonWrapper = {
    val cptsRenamed = Remapper.applyRemapping(map, inducedTrans.cv.components)
    val commonMissingPids =
      commonMissingRefs(inducedTrans.preCpts, cptsRenamed).toArray

// FIXME: need new inducedTrans, setting cpts
    MissingCommonWrapper(inducedTrans, commonMissingPids, views)
  }

}
