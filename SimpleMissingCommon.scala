package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
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
class SimpleMissingCommon(
  servers: ServerStates, cpts1: Cpts, cpts2: Cpts, family: Int, id: Int)
    extends MissingCommon(servers,cpts1, /*cpts2,*/ family, id){

  Profiler.count("SimpleMissingCommon")

  require(cpts2(0).processIdentities.contains(pid))

  /* Overview of main functions.
   * 
   * updateMissingViews       
   * |--removeViews
   * 
   * updateMissingCandidatesWith
   * |- getMissingCandidates
   * |- add
   */

  /** Highlight if this relates to the relevant instance. 
    * servers = [107(N0) || 109(N1) || 110() || 114(T0) || 119() || 1()]
    * cpts1 = [75(T0,N0,N1,N2) || 14(N0,N1,Null)]
    * cpts2 = [31(T1,N3,N2,N1) || 10(N3,Null,N2)] */
  // @inline private def highlight = false && 
  //   (pid == (0,1) || pid == (0,2)) && Transition.highlightPreServers(servers) && 
  //   Transition.highlightPreCpts(cpts1) && {
  //     val princ2 = cpts2(0)
  //     princ2.cs == 31 && princ2.ids.sameElements(Array(1,3,2,1)) && {
  //       val second2 = cpts2(1)
  //       second2.cs == 10 && second2.ids.sameElements(Array(3,-1,2))
  //     }
  //   }

  /** Each value cands of type MissingComponents represents that if
    * (servers,cpts) is added to the ViewSet for each cpts in cands, then this
    * obligation will be discharged.  Each corresponds to a particular
    * component state c for which condition (1) is satisfied; cands contains
    * those components corresponding to conditions (2) and (3).  Each such
    * cands is sorted (wrt StateArray.lessThan), and uses values registered in
    * StateArray.  */
  import MissingCommon.MissingComponents // = Array[Cpts]

  def showMissingComponents(cptsList: MissingComponents) =
    cptsList.map(StateArray.show).mkString("; ")

  /** When any element of missingCandidates is satisfied, then this obligation
    * will be discharged.  Each MissingComponents within the array is sorted
    * (wrt StateArray.lessThan).  missingCandidates is set to null when this
    * is done. */
  private[this] var missingCandidates = new Array[MissingComponents](0)
  /* We maintain the invariant that, if this is the first non-done MissingCommon
   * in a MissingInfo, then the first element of each list is either missing
   * from the current view set, or in the set of new views being considered on
   * the current ply.  The MissingInfo object containing this object will be
   * registered against those first elements in the EffectOnStore. */

  /** Clear missingCandidates, to reclaim memory. */
  @inline protected def clear = missingCandidates = null

  /** The heads of the missing candidates.  The corresponding MissingInfo should
    * be registered against these in EffectOnStore.mcNotDoneStore. */
  def missingHeads: Array[Cpts] = synchronized{ missingCandidates.map(_(0)) }

  import MissingCommon.CptsBuffer // = ArrayBuffer[Cpts]

  /** Remove the maximum prefix of mc consisting of elements of views.  If any
    * is empty, record that this is done; otherwise add the next view to
    * toRegister. */
  @inline private 
  def removeViews(mc: MissingComponents, views: ViewSet, toRegister: CptsBuffer)
      : MissingComponents = {
    val mc1 = remove(mc, views)
    if(mc1 == null) setDone    // This is now satisfied
    else if(mc != mc1) toRegister += mc1(0)   
    // If unchanged, no need to re-register.
    mc1
  }

  import MissingCommon.{Eq,Sub,Sup,Inc,compare}

  /** Update missingCandidates based on views.  Remove elements of views from
    * the front of each.  If any is now empty, then mark this as satisfied.
    * Return views against which this should now be registered, or null if
    * done. */
  def updateMissingViews(views: ViewSet): CptsBuffer = synchronized{
    // if(highlight) println(s"updateMissingViews $pid "+
    //   missingCandidates.map(showMissingComponents))
    if(done){ assert(missingCandidates == null); null } 
    else{
      val toRegister = new CptsBuffer; val len = missingCandidates.length
      // Note: it's possible that missingCandidates is empty here
      val newMC = new Array[MissingComponents](len); var i = 0
      // Which missingComponents have been superseded by others?
      val superseded = new Array[Boolean](len); var count = len
      while(i < len && !done){
        val mc1 = removeViews(missingCandidates(i), views, toRegister); 
// IMPROVE: Either make use of the following or remove it. 
        if(!done){
          // Test if mc1 implied by another value in newMC, or vice versa
          var j = 0
          while(j < i && !superseded(i)){
            if(!superseded(j)){
              val cmp = compare(newMC(j), mc1)
              if(cmp != Inc){
                Profiler.count("SMC.updateMissingView superseded")
                // About 0.025 cases per MissingCommon for lazySet; much
                // better for lockFreeSet
                if(cmp == Sup){ superseded(j) = true; count -= 1 }
                else{ superseded(i) = true; count -= 1 } // cmp == Sub or Eq
              }
            }
            j += 1
          } // end of inner while loop
        } // end of if(!done)
        newMC(i) = mc1; i += 1
      } // end of outer while loop
      if(done){ assert(missingCandidates == null);  null }
      else{ 
// FIXME
        if(true || count == len) missingCandidates = newMC
        else{
          // Copy the non-superseded elements of newMC into missingCandidates
          val toStore = new Array[MissingComponents](count); var i = 0; var j = 0
          while(i < len){
            if(!superseded(i)){ toStore(j) = newMC(i); j += 1 }
            i += 1
          }
          assert(j == count); missingCandidates = toStore
        }
// IMPROVE: only need to register those not superseded.
        toRegister
      }
    }
  }

  /** Update missingCandidates to include lists of missing components
    * corresponding to instantiating the missing component with c.  Add to cb
    * the components that this needs to be registered against in the
    * EffectOnStore, namely missingHeads.  Return true if this is now
    * done.  */
  @inline protected
  def updateMissingCandidatesWith(c: State, views: ViewSet, cb: CptsBuffer)
      : Boolean = {
    val missing = getMissingCandidates(c, views)
    // Note: missing is compatible with StateArray, sorted
    if(missing.isEmpty) true // found = true
    else{
      // Note we have to register the corresponding MissingInfo against
      // missing.head, whether or not the add succeeded, because this
      // might be shared between MissingInfos.
      add(missing); cb += missing.head; false
    }
  }

  /** All relevant renamings of cpt1 as a possible instantiation of the common
    * missing component.  Identity on params of servers and princ1, but
    * otherwise mapping to parameters of a secondary component c2 of cpts1 or
    * cpts2 only if there is already a cross reference between cpt1 and c2 (in
    * either direction).  */
  protected def remapToJoin(cpt1: State) : Array[State]  = 
    Unification.remapToJoin(servers, princ1, cpts1, cpts2, cpt1)

  /** Find the missing components that (with servers) are necessary to complete
    * this for a particular candidate state c.  Return an array containing
    * each of the following that is not currently in views: (1) cpts2(0) || c;
    * and (2) if c has a reference to a secondary component c2 of cpts1 or
    * cpts2, then c || c2 (renamed).  The array is sorted (wrt
    * StateArray.lessThan) and uses values registered in StateArray.  */
  @inline private 
  def getMissingCandidates(c: State, views: ViewSet): MissingComponents = {
    val requiredCpts = MissingCommon.requiredCpts(servers, cpts1, cpts2, c)
    unseen(requiredCpts, views)
  }

  import MissingCommon.{Eq,Sub,Sup,Inc}

  /** Add mCpts to missingCandidates if no subset is there already; remove any
    * superset of mCand.  Pre: mCpts is sorted and all elements are registered
    * in StateArray.  */
  private[this] def add(mCpts: MissingComponents): Unit = {
    assert(!done); missingCandidates = addTo(missingCandidates, mCpts)
  }

  /** Is mCand sorted, without repetitions. */
  private def isSorted(mCpts: MissingComponents): Boolean = {
    var i = 0
    while(i < mCpts.length-1 && StateArray.compare(mCpts(i), mCpts(i+1)) < 0)
      i += 1
    i == mCpts.length-1
  }

  override def toString = 
    s"MissingCommon($servers, ${StateArray.show(cpts1)},\n"+
      s"  ${StateArray.show(cpts2)}, $pid)\n"+
      s"  missingCandidates = "+
      missingCandidates.map(showMissingComponents).mkString("\n    ")+
      s"\n  done = $done\n" // theLog = "+theLog.reverse.mkString("\n    ")+"\n"

  /* Note: we avoid creating duplicates of MissingCommon objects, so we can use
   * object equality. */

  // /** Ordering on MissingCommon values.  Return a value x s.t.: x < 0 if this <
  //   * that; x == 0 when this == that; x > 0 when this > that. */
  // def compare(that: MissingCommon) = {
  //   // Note: refers only to parameters, so locking not necessary.
  //   /* The following makes comparison more efficient, but makes the ordering
  //    * nondeterministic (varying from one run to another), and so makes the
  //    * final sizes of the stores nondeterministic.
  //   val hashComp = compareHash(hashCode, that.hashCode)
  //   if(hashComp != 0) hashComp
  //   else{ */
  //   val ssComp = servers.compare(that.servers)
  //   if(ssComp != 0) ssComp
  //   else{
  //     val cmp1 = StateArray.compare(cpts1, that.cpts1)
  //     if(cmp1 != 0) cmp1
  //     else{
  //       val cmp2 = StateArray.compare(cpts2, that.cpts2)
  //       if(cmp2 != 0) cmp2
  //       else{
  //         val familyDiff = family - that.family // pid._1 - that.pid._1
  //         if(familyDiff != 0) familyDiff
  //         else id - that.id //  pid._2 - that.pid._2
  //       }
  //     }
  //   }
  // }

}

