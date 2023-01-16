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
  servers: ServerStates, cpts1: Cpts, cpts2: Cpts, family: Int, id: Int) 
    extends MissingCommon(servers,cpts1, cpts2, family, id){
  import MissingCommon.CptsBuffer // = ArrayBuffer[Cpts]

  import MissingCommon.MissingComponents // = Array[Cpts]

  /** Each componentCandidate(i) represents a component state to instantiate the
    * common missing component.  The requirements involving cpts1 are not yet
    * satisfied. */
  private[this] var componentCandidate = new Array[State](0)

  /** Each missingComponentsForCpts(i) represents the views required to satisfy
    * the requirements involving componentCandidate(i) and cpts1.  */
  private[this] var missingComponentsForCpts1 = new Array[MissingComponents](0)

  /* Inv: componentCandidate.length == missingComponentsForCpts1. */

  /** Each missingComponentsForCpts(i) represents a set of views that will allow
    * this constraint to be satisfied.  Each represents a set of views
    * concerning cpts2.  */
  private[this] var missingComponentsForCpts2 = new Array[MissingComponents](0)

  // NOTE: I think we might have to store the corresponding oldCpts

  /** Record that this is now done.  Also clear arrays to reclaim memory. */
  def setDone = { 
    setDoneFlag; componentCandidate = null; missingComponentsForCpts1 = null;
    missingComponentsForCpts2 = null
  }
  
  /** The heads of the missing candidates.  The corresponding MissingInfo should
    * be registered against these in EffectOnStore.mcNotDoneStore. */
  def missingHeads: Array[Cpts] = synchronized{
    missingComponentsForCpts1.map(_(0)) ++ missingComponentsForCpts2.map(_(0))
  }

  /** Have the arrays been nulled out?  Used in assertions. */
  @inline private def nulled = 
    missingComponentsForCpts1 == null && componentCandidate == null && 
      missingComponentsForCpts2 == null

  /** Update missing candidates based on views.  Remove elements of views from
    * the front of each.  If any is now empty, then mark this as satisfied.
    * Return views against which this should now be registered, or null if
    * done. */
  def updateMissingViews(views: ViewSet): CptsBuffer = synchronized{
    if(done){ assert(nulled); null }
    else{
      val toRegister = new CptsBuffer
      // Update missingComponentsForCpts1 based on views; toTransfer is the
      // candidate missing components for which this subrequirement is now
      // satisfied.  Add new heads to toRegister.
      val toTransfer = updateMissingViews1(views, toRegister)
      assert(!done)
      // For each element of toTransfer, find the views required for cpts2.  
      // If any is empty, this is now done.
      val newMissingCandidates2 = new Array[Array[Cpts]](toTransfer.length)
      var i = 0; val toTransferLen = toTransfer.length
      while(i < toTransferLen && !done){
        val c = toTransfer(i)
        val required = MissingCommon.getRequiredCpts(servers, cpts2, c)
        val missing = unseen(required, views)
        if(missing.isEmpty) setDone
        else{ newMissingCandidates2(i) = missing; toRegister += missing.head }
      }
      if(done) null // an element of toTransfer is complete
      else{
        // Update each element of missingComponentsForCpts2
        val count = update(missingComponentsForCpts2, views, toRegister)
        // IMPROVE: abort update early if null found
        val len2 = missingComponentsForCpts2.length
        if(count < len2){
          // One of the elements of missingComponentsForCpts2 is now
          // satisfied, so this is now done.
          setDone; null 
        }
        else{
          // Add newMissingCandidates2 to missingComponentsForCpts2
          if(toTransferLen > 0)
            missingComponentsForCpts2 =
              missingComponentsForCpts2 ++ newMissingCandidates2
          // IMPROVE: use below
          toRegister
        }
      }
    }
  }

  // Add newMissingCandidates2 to missingComponentsForCpts2
          // val newCpts = new Array[MissingComponents](count+toTransferLen)
          // var j = 0
          // for(i <- 0 until len2){
          //   val cpts = missingComponentsForCpts2(i)
          //   if(cpts != null){ newCpts(j) = cpts; j += 1 }
          // }
          // assert(j == count)
          // for(i <- 0 until toTransferLen)
          //   newCpts(count+i) = newMissingCandidates2(i)
          // missingComponentsForCpts2 = newCpts

  /** Update each entry of missingComponents based on views.  Remove the longest
    * prefix of each that are in views.  Add to toRegister those components
    * against which this should now be registered. */
  @inline private def update(missingComponents: Array[MissingComponents],
    views: ViewSet, toRegister: CptsBuffer)
      : Int = {
    var i = 0; val len = missingComponents.length; var count = 0
    while(i < len){ 
      val mc = missingComponents(i); val mc1 = remove(mc, views)
      missingComponents(i) = mc1
      if(mc1 != null) { 
        if(true || mc1 != mc) toRegister += mc1(0) // IMPROVE
        count += 1
      }
      i += 1
    }
    count
  }

  /** Update missingComponentsForCpts1 based on views.  Return the missing
    * component candidates for which these views are now all found. */
  private def updateMissingViews1(views: ViewSet, toRegister: CptsBuffer)
      : ArrayBuffer[State] = {
    // Update each entry; count is number to retain
    val count = update(missingComponentsForCpts1, views, toRegister)
    val len = missingComponentsForCpts1.length
    val toTransfer = new ArrayBuffer[State]
    // Filter out those elements of missingComponentsForCpts1 that are now
    // null, and add the corresponding candidate missing component to
    // toTransfer.
    if(count < len){
      // Create new arrays, and copy across those to retain
      val newComponentCandidate = new Array[State](count)
      val newCpts1 = new Array[MissingComponents](count); var j = 0; var i = 0
      while(i < len){
        val cpts =  missingComponentsForCpts1(i)
        if(cpts != null){
          newComponentCandidate(j) = componentCandidate(i)
          newCpts1(j) = cpts; j += 1
        }
        else toTransfer += componentCandidate(i)// will transfer
        i += 1
      }
      assert(j == count); componentCandidate = newComponentCandidate
      missingComponentsForCpts1 = newCpts1
    }
    toTransfer
  }

  

  /** Update missingCandidates to include lists of missing components
    * corresponding to instantiating c with a renaming of cpt1.  Add to vb the
    * views that this needs to be registered against in the EffectOnStore,
    * namely missingHeads.
    * 
    * Pre: views contains a view servers || cpts1(0) || cpt1 to
    * instantiate clause (1) of this.
    * 
    * @return true if this is now complete. */
  // def updateMissingCandidates(cpt1: State, views: ViewSet, vb: CptsBuffer)
  //     : Boolean = ???

  protected
  def updateMissingCandidatesWith(c: State, views: ViewSet, cb: CptsBuffer)
      : Boolean = ???
}
