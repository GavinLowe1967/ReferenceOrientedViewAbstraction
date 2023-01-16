package ViewAbstraction

import MissingCommon.Cpts // = Array[State]

import scala.collection.mutable.ArrayBuffer

/** The representation of the obligation to find a component state c with
  * identity pid = (family,id) such that (1) servers || cpts1(0) || c is in
  * the ViewSet; (2) servers || cpts2(0) || c is in the ViewSet; (3) if c has
  * a reference to a secondary component c2 of cpts1 or cpts2, or vice versa,
  * then servers || c || c2 is in ViewSet (modulo renaming).  This corresponds
  * to condition (c) in the definition of induced transitions with restricted
  * views, for a common missing component with identity pid.  Here cpts1
  * corresponds to the pre-state of a transition, and cpts2 to the view acted
  * upon. */
class TwoStepMissingCommon(
  val servers: ServerStates, cpts1: Cpts, cpts2: Cpts, family: Int, id: Int) 
    extends MissingCommon{
  import MissingCommon.CptsBuffer // = ArrayBuffer[Cpts]

  import MissingCommon.MissingComponents // = Array[Cpts]

  /** Each componentCandidate(i) represents a component state to instantiate the
    * common missing component.  The requirements involving cpts1 are not yet
    * satisfied. */
  private[this] var componentCandidate = new Array[State](0)

  /** Each missingCandidatesForCpts(i) represents the views required to satisfy
    * the requirements involving componentCandidate(i) and cpts1.  */
  private[this] var missingCandidatesForCpts1 = new Array[MissingComponents](0)

  /* Inv: componentCandidate.length == missingCandidatesForCpts1. */

  /** Each missingCandidatesForCpts(i) represents a set of views that will allow
    * this constraint to be satisfied.  Each represents a set of views
    * concerning cpts2.  */
  private[this] var missingCandidatesForCpts2 = new Array[MissingComponents](0)

  // NOTE: I think we might have to store the corresponding oldCpts
  
  /** The heads of the missing candidates.  The corresponding MissingInfo should
    * be registered against these in EffectOnStore.mcNotDoneStore. */
  def missingHeads: Array[Cpts] = synchronized{
    missingCandidatesForCpts1.map(_(0)) ++ missingCandidatesForCpts2.map(_(0))
  }

  /** Update this based on using cv to instantiate servers || princ1 || c.
    * @return a CptsBuffer containing those Views against which this needs to
    * be registered, namely missingHeads; or null if this is done. */
  def updateWithNewMatch(cv: ComponentView, views: ViewSet)
      : CptsBuffer = ???

  /** Have the arrays been nulled out?  Used in assertions. */
  @inline private def nulled = 
    missingCandidatesForCpts1 == null && componentCandidate == null && 
      missingCandidatesForCpts2 == null

  /** Update missing candidates based on views.  Remove elements of views from
    * the front of each.  If any is now empty, then mark this as satisfied.
    * Return views against which this should now be registered, or null if
    * done. */
  def updateMissingViews(views: ViewSet): CptsBuffer = synchronized{
    if(done){ assert(nulled); null }
    else{
      val toRegister = new CptsBuffer
      val toTransfer = updateMissingViews1(views, toRegister)
      if(done){ assert(nulled); null }
      else{
        // TODO: update missingCandidatesForCpts2
        // assert(missingCandidatesForCpts1.isEmpty || toRegister.nonEmpty)

        // For each element of toTransfer, find the views required for cpts2
        // and add to missingCandidatesForCpts2.  Update
        // missingCandidatesForCpts2 based on views.

        toRegister
      }
    }
  }

  /** Update missingCandidatesForCpts1 based on views.  */
  private def updateMissingViews1(views: ViewSet, toRegister: CptsBuffer)
      : ArrayBuffer[State] = {
    var i = 0; val len = missingCandidatesForCpts1.length
    // Bit map showing which entries to retain, and their count
    val retain = new Array[Boolean](len); var count = 0
    val toTransfer = new ArrayBuffer[State]
    while(i < len){ // IMPROVE: && !done ???
      val mc = missingCandidatesForCpts1(i); val mc1 = remove(mc, views)
      if(mc1 == null) toTransfer += componentCandidate(i) // will transfer
      else{ 
        if(true || mc1 != mc) toRegister += mc1(0) // IMPROVE
        retain(i) = true; count += 1
      }
      i += 1
    }
    if(!done && count < len){
      // Create new arrays, and copy across those to retain
      val newComponentCandidate = new Array[State](count)
      val newCpts1 = new Array[MissingComponents](count)
      var j = 0; i = 0
      while(i < len){
        if(retain(i)){
          newComponentCandidate(j) = componentCandidate(i)
          newCpts1(j) = missingCandidatesForCpts1(i); j += 1
        }
        i += 1
      }
      assert(j == count); componentCandidate = newComponentCandidate
      missingCandidatesForCpts1 = newCpts1
    }
    toTransfer
  }

  /** The constraints concerning cpts1 are now done for c.  Generate the
    * constriants concerning cpts2. */
  private def cpts1Done(c: State, views: ViewSet) = {
    val mc = MissingCommon.getRequiredCpts(servers, cpts2, c)
    ??? // TODO
  }


  

}
