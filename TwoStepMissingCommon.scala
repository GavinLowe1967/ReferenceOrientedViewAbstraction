package ViewAbstraction

import MissingCommon.Cpts // = Array[State]

import scala.collection.mutable.ArrayBuffer
import ox.gavin.profiling.Profiler

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

  Profiler.count("TwoStepMissingCommon")

  /* Overview of main functions.
   * 
   * updateMissingViews  
   * |--updateMissingViews1
   * |  |-update
   * |--update
   * 
   * updateMissingCandidatesWith
   */

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

  /** Clear data structures, to reclaim memory. */
  @inline protected def clear: Unit = {
    componentCandidate = null; missingComponentsForCpts1 = null;
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
        i += 1
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
          // IMPROVE: use below; and remove subsets
          toRegister
        }
      }
    }
  }

  // KEEP
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
    assert(componentCandidate.length == len)
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
    * corresponding to instantiating the missing component with c.  Add to cb
    * the components that this needs to be registered against in the
    * EffectOnStore, namely missingHeads.  Return true if this is now
    * done.  */
  protected
  def updateMissingCandidatesWith(c: State, views: ViewSet, cb: CptsBuffer)
      : Boolean = {
    val required1 = MissingCommon.getRequiredCpts(servers, cpts1, c)
    val missing1 = unseen(required1, views)
    if(missing1.nonEmpty){ 
      // Add to missingComponentsForCpts1 if not implied by one there
      addToMissingComponents1(missing1, c)
      cb += missing1.head // IMPROVE: only if !found ??
      false
    } // end of if(missing1.nonEmpty)
    else{
      // Is this the first time we've got past the first stage?
      if(missingComponentsForCpts2.isEmpty)
        Profiler.count("TwoStepMissingCommon.step2")
      // Consider requirements for cpts2
      val required2 = MissingCommon.getRequiredCpts(servers, cpts2, c)
      val missing2 = unseen(required2, views)
      if(missing2.nonEmpty){
        // Add to missingComponentsForCpts2 if not implied by one there
        addToMissingComponents2(missing2)
        cb += missing2.head // IMPROVE: only if !found ??
        false
      }
      else true 
    }
  }

  /** Add cpts to missingComonentsForCpts1, associated with c.  */
  @inline private 
  def addToMissingComponents1(cpts: MissingComponents, c: State) = {
    // Test if c in componentCandidate
    var i = 0; val len = componentCandidate.length
    while(i < len && componentCandidate(i) != c) i += 1
    if(i == len){
      missingComponentsForCpts1 :+= cpts; componentCandidate :+= c
    }
    else{
      // Does this case ever happen? 
      Profiler.count("TwoStepMissingCommon.Existing")
      // I'm unsure about the following.  It might be a superset
      assert(missingComponentsForCpts1(i).sameElements(cpts),
        s"c = $c;\ncpts = "+cpts.mkString("; ")+
          "\nexisting = "+missingComponentsForCpts1(i).mkString("; "))
    }
  }

  /** Add cpts to missingComonentsForCpts1, associated with c, if not implied by
    * a value there.  Purge entries implied by cpts.  */
//   @inline private 
//   def OLDaddToMissingComponents1(cpts: MissingComponents, c: State) = {
// //IS THIS RIGHT?  THEY MIGHT CORRESPOND TO DIFFERENT COMPONENTS
//     ???
//     val (found, toRetain, retainCount) =
//       compareMissingComponents(missingComponentsForCpts1, cpts)
//     if(!found || retainCount < missingComponentsForCpts1.length){
//       val newLen = if(found) retainCount else retainCount+1
//       val newMC = new Array[MissingComponents](newLen)
//       val newCC = new Array[State](newLen)
//       assert(newMC.length > 0); var j = 0; var i = 0
//       while(i < missingComponentsForCpts1.length){
//         if(toRetain(i)){
//           newMC(j) = missingComponentsForCpts1(i);
//           newCC(j) = componentCandidate(i); j += 1
//         }
//         i += 1
//       } // end of while
//       assert(j == retainCount)
//       if(!found){ newMC(retainCount) = cpts; newCC(j) = c }
//       missingComponentsForCpts1 = newMC; componentCandidate = newCC
//     } // end of if(!found ...)
//     // missingComponentsForCpts1 :+= missing1; componentCandidate :+= c
//   }


  /** Add cpts to missingComponentsForCpts2 if it's not implied by any value
    * there.  Remove any value implied by cpts. */
  @inline private def addToMissingComponents2(cpts: MissingComponents) = {
    // Profiler.count("TwoStepMissingCommon.addToMissingComponents2:"+
    //   missingComponentsForCpts2.isEmpty)
    // Add to missingComponentsForCpts2 if not implied by one there
    missingComponentsForCpts2 = addTo(missingComponentsForCpts2, cpts)

    // val (found, toRetain, retainCount) =
    //   compareMissingComponents(missingComponentsForCpts2, cpts)
    // if(!found || retainCount < missingComponentsForCpts2.length){
    //   val newLen = if(found) retainCount else retainCount+1
    //   val newMC = new Array[MissingComponents](newLen)
    //   assert(newMC.length > 0); var j = 0; var i = 0
    //   while(i < missingComponentsForCpts2.length){
    //     if(toRetain(i)){ newMC(j) = missingComponentsForCpts2(i); j += 1 }
    //     i += 1
    //   } // end of while
    //   assert(j == retainCount)
    //   if(!found) newMC(retainCount) = cpts
    //   missingComponentsForCpts2 = newMC
    // } // end of if(!found ...)
    // missingComponentsForCpts2 :+= missing2
  }

}
