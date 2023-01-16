package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
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
class SimpleMissingCommon(
  val servers: ServerStates, cpts1: Cpts, cpts2: Cpts, family: Int, id: Int)
    extends MissingCommon{

  // assert(cpts1.eq(StateArray(cpts1))); assert(cpts2.eq(StateArray(cpts2)))

  /* Overview of main functions.
   * 
   * updateMissingViews       (called from MissingInfo)
   * |--removeViews
   * 
   * updateWithNewMatch      (called from MissingInfo)
   * |--updateMissingCandidates
   *    |--Unification.remapToJoin
   *    |--getMissingCandidates
   *       |--add
   * 
   * done, missingHeads, matches, sanityCheck, compare, size
   */

  @inline private def pid = (family, id)

  @inline private def princ1 = cpts1(0)

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

  require(princ1.processIdentities.contains(pid) && 
    cpts2(0).processIdentities.contains(pid))

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

  //import MissingCommon.{DoneMask,CountedMask}

  // /** Variable encapsulating some flags. */
  // private var flags = 0

  // /** Is this constraint satisfied? */
  // @inline private def isDone = (flags & DoneMask) != 0

  // /** Record that this constraint is satisfied. */
  // @inline private def setDoneFlag = flags = (flags | DoneMask)

  // /** Is this constraint satisfied? */
  // @inline def done = synchronized{ isDone }

  // Log for debugging
  // import MissingCommon.{MCEvent, AddMC, UpdateMC, SetDoneMC,
  //   MissingCandidateSuccess, UMCRepeat}

  /** Logging for debugging.  Currently turned on. */
  // def log(e: MCEvent) = {} 

  /** Record that this is now done.  Also clear missingCandidates and
    * doneMissingCandidates to reclaim memory. */
  def setDone = { 
    setDoneFlag; missingCandidates = null
    doneMissingCandidates = null // ; log(SetDoneMC)
  }

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
    // If unchanged, no need to re-register (???).
    mc1


/*
    // For simplicity, we convert to a List, and back to an Array at the end.
    // This could be improved.
    var mc1 = mc.toList
    while(mc1.nonEmpty && views.contains(servers, mc1.head)) mc1 = mc1.tail
    // log(UpdateMC(mc, mc1.toArray, ply))
    if(mc1.isEmpty) setDone    // This is now satisfied
    else toRegister += mc1.head
    mc1.toArray
 */
  }

  /** Update missingCandidates based on views.  Remove elements of views from
    * the front of each.  If any is now empty, then mark this as satisfied.
    * Return views against which this should now be registered, or null if
    * done. */
  def updateMissingViews(views: ViewSet): CptsBuffer = synchronized{
    // if(highlight) println(s"updateMissingViews $pid "+
    //   missingCandidates.map(showMissingComponents))
    if(done){ assert(missingCandidates == null); null } 
    else{
      val toRegister = new CptsBuffer
      // Note: it's possible that missingCandidates is empty here
      val newMC = missingCandidates.map(mc => removeViews(mc, views, toRegister))
      if(done){ assert(missingCandidates == null);  null }
      else{
        missingCandidates = newMC
        // NOT TRUE
        // assert(missingCandidates.isEmpty || toRegister.nonEmpty, 
        //   s"updateMissingViews with\n${missingCandidates}")
        toRegister
      }
    }
  }

  /** Is cv a possible match to clause (1), i.e. does it match servers ||
    * cpts1(0) || c? */
  @inline def matches(cv: ComponentView) = synchronized{
    cv.servers == servers && cv.components(0) == princ1
  }
  // IMPROVE: can we also ensure that cv.components(1).processIdentity == pid?

  /** Update this based on using cv to instantiate servers || princ1 || c.  
    * @return a CptsBuffer containing those Views against which this needs to
    * be registered, namely missingHeads; or null if this is done. */
  def updateWithNewMatch(cv: ComponentView, views: ViewSet)
      : CptsBuffer = synchronized{
    require(matches(cv))
    // if(highlight) println(s"updateWithNewMatch($cv) $pid")
    if(!done){
      val cpt1 = cv.components(1); val vb = new CptsBuffer
      if(cpt1.hasPID(family,id)){
        // Remap cpt1 to a normal form
        val cpt1Norm = Remapper.remapWRT(servers, cpts1, cpts2, cpt1) 
        if(updateMissingCandidates(cpt1Norm, views, vb)){ 
          //log(MissingCommon.UpdateWithNewMatchSuccess(cv, ply))
          setDone; null
        }
        else vb
      }
      else vb
    }
    else null
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
  @inline 
  def updateMissingCandidates(cpt1: State, views: ViewSet, vb: CptsBuffer)
      : Boolean = {
    //if(highlight) println(s"updateMissingCandidates($cpt1) $pid")
    require(!done && cpt1.hasPID(family,id))
    if(isNewUMCState(cpt1)){
      // All relevant renamings of cpt1: identity on params of servers and
      // princ1, but otherwise either to other params of cpts1 or cpts2, or to
      // fresh values.  
      val renames = Unification.remapToJoin(servers, princ1, cpts1, cpts2, cpt1)
      var i = 0; var found = false
      while(i < renames.length && !found){
        val c = renames(i); i += 1
        if(true || isNewUMCRenamedState(c)){ // IMPROVE
          val missing = getMissingCandidates(c, views) 
          // Note: missing is compatible with StateArray, sorted
          if(missing.isEmpty){ 
            /*log(MissingCandidateSuccess(cpt1, c));*/ found = true 
          }
          else{
            // Note we have to register the corresponding MissingInfo against
            // missing.head, whether or not the add succeeded, because this
            // might be shared between MissingInfos.
            add(missing); vb += missing.head 
          }
        }
      } // end of while loop
      found
    } // end of if isNewUMCState
    else{ 
      // This update has previously been done, but we might need to
      // re-register the MissingInfo object, because of sharing.  The
      // following might be a bit pessimistic.  IMPROVE: store the relevant
      // values from one instance to reuse in the next.
      // log(UMCRepeat(cpt1))
// IMPROVE: I think the commented-out code is better, but needs to deal with the
// case that vb1 is null.  
/*    val vb1 = updateMissingViews(views); assert(vb1 != null, this)
      vb ++= vb1  */
      for(cpts <- missingHeads) if(!views.contains(servers, cpts)) vb += cpts
      false
    }
  }

  /** Find the missing components that (with servers) are necessary to complete
    * this for a particular candidate state c.  Return an array containing
    * each of the following that is not currently in views: (1) cpts2(0) || c;
    * and (2) if c has a reference to a secondary component c2 of cpts1 or
    * cpts2, then c || c2 (renamed).  The array is sorted (wrt
    * StateArray.lessThan) and uses values registered in StateArray.  */
  @inline private 
  def getMissingCandidates(c: State, views: ViewSet): MissingComponents = {
    //if(highlight) println(s"getMissingCandidates($c)")
    val missing = new ArrayBuffer[Array[State]] // missing necessary views
    /* Is cpts not already in missing? */
    @inline def isNew(cpts: Array[State]) = {
      var i = 0; val len = missing.length
      // Note: we're using canonical Array[State]s, so reference equality
      while(i < len && missing(i) != cpts) i += 1
      i == len
    }
    val requiredCpts = MissingCommon.requiredCpts(servers, cpts1, cpts2, c)
    var i = 0
    while(i < requiredCpts.length){
      val cpts = requiredCpts(i); i += 1
      // assert(StateArray.isCanonical(cpts))
      if(!views.contains(servers, cpts) && isNew(cpts))
        // !missing.exists(_.sameElements(cpts)))
        missing += cpts
    }
    missing.toArray.sortWith(StateArray.lessThan)
  }

  /** Representation of the States for which
    * MissingCommon.updateMissingCandidates has been executed on this.  State
    * st is represented by st.index+1. */
  private var doneMissingCandidates = new collection.IntSet

  /** Called by MissingCommon.updateMissingCandidates when updating this with
    * st.  Return true if this is the first such instance for st. */
  private def isNewUMCState(st: State): Boolean = {
    assert(st.index >= 0); doneMissingCandidates.add(st.index+1)
  }

  /** States for which the loop of MissingCommon.updateMissingCandidates has
    * been executed, i.e. states instantiating c there. */
  // private val doneMissingCandidatesRenamed: HashSet[State] = null
  //  IMPROVE: not used at present

  /** Called by MissingCommon.updateMissingCandidates when updating this with
    * st.  Return true if this is the first such instance for st instantiating
    * c.  Not currently used. */
  private def isNewUMCRenamedState(st: State): Boolean = ???
  // doneMissingCandidatesRenamed.add(st)

  import MissingCommon.{Eq,Sub,Sup,Inc}

  /** Add mCpts to missingCandidates if no subset is there already; remove any
    * superset of mCand.  Return true if successful.  Pre: mCpts is sorted and
    * all elements are registered in StateArray.  */
  private[this] def add(mCpts: MissingComponents): Boolean = {
    assert(!done)
    // assert(mCpts.forall(cpts => cpts.eq(StateArray(cpts))))
    // require(isSorted(mCpts), mCpts.map(StateArray.show)) 
    // Traverse missingCandidates.  We aim to retain any that is  not a proper
    // superset of mCpts.  Record which to retain in toRetain.
    val toRetain = new Array[Boolean](missingCandidates.length); 
    var i = 0; var retainCount = 0 // number to retain
    var found = false // true if missingCandidates includes a subset of mCpts
    while(i < missingCandidates.length){
      val mCpts1 = missingCandidates(i)
      // Note: mCpts is local; this is locked; so neither of following
      // parameters can be mutated by a concurrent thread.
      val cmp = MissingCommon.compare(mCpts1, mCpts)
      if(cmp != Sup){ toRetain(i) = true; retainCount += 1}
      found ||= cmp == Sub || cmp == Eq // mCpts can't be replaced by mCpts1
      i += 1
    }
    // Update missingCandidates, retaining elements of missingCandidates as
    // indicated by toretain.
    val newMC = 
      new Array[MissingComponents](if(found) retainCount else retainCount+1)
    assert(newMC.length > 0); var j = 0; i = 0
    while(i < missingCandidates.length){
      if(toRetain(i)){ newMC(j) = missingCandidates(i); j += 1 }
      i += 1
    }
    assert(j == retainCount)
    if(!found) newMC(retainCount) = mCpts
    missingCandidates = newMC; !found
  }

  /** Is mCand sorted, without repetitions. */
  private def isSorted(mCpts: MissingComponents): Boolean = {
    var i = 0
    while(i < mCpts.length-1 && StateArray.compare(mCpts(i), mCpts(i+1)) < 0)
      i += 1
    i == mCpts.length-1
  }

  // /** Sanity check that no head element of missingCandidates is in views. */
  // def sanityCheck(views: ViewSet) = {
  //   if(done) assert(missingCandidates.isEmpty, 
  //     s"missingCandidates = \n"+missingCandidates.mkString("\n"))
  //   else for(mcs <- missingCandidates){
  //     val v = new ComponentView(servers, mcs.head)
  //     assert(!views.contains(v), s"\n$this\n  still contains $v")
  //   }
  // }

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

  // /** Has this been counted for profiling purposes? */
  // @inline private def counted = (flags & CountedMask) != 0

  // /** Record that this has been counted. */
  // @inline private def setCounted = flags = (flags | CountedMask)

  // /** A measure of the size of this: the number of ComponentViews stored.  If
  //   * size has already been called, then return 0 to avoid double-counting. */
  // def size = {
  //   if(counted || missingCandidates == null) 0
  //   else{
  //     setCounted; var i = 0; var size = 0
  //     while(i < missingCandidates.length){
  //       size += missingCandidates(i).length; i += 1
  //     }
  //     size
  //   }
  // }
}

