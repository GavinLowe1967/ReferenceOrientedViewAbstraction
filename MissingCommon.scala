package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet,HashMap}

/** The representation of the obligation to find a component state c with
  * identity pid such that (1) servers || cpts1(0) || c is in the ViewSet; (2)
  * servers || cpts2(0) || c is in the ViewSet; (3) if c has a reference to a
  * secondary component c2 of cpts1 or cpts2, then servers || c || c2 is in
  * ViewSet (modulo renaming).  This corresponds to condition (c) in the
  * definition of induced transitions with restricted views. */
class MissingCommon(
    val servers: ServerStates, val cpts1: Array[State], val cpts2: Array[State],
    val pid: ProcessIdentity){
  /* Overview of main functions.
   * 
   * updateMissingViews       (called from MissingInfo)
   * |--removeViews
   * 
   * updateWithNewMatch      (called from MissingInfo)
   * |--MissingCommon.updateMissingCandidates
   * 
   * add                    (called from MissingCommon.updateMissingCandidates
   */

  private val princ1 = cpts1(0)

  // def key = (servers, princ1)

  require(princ1.processIdentities.contains(pid) && 
    cpts2(0).processIdentities.contains(pid))

  /** Each value cands of type MissingCandidates represents that if all the
    * elements of cands are added to the ViewSet, then this obligation will be
    * discharged.  Each corresponds to a particular component state c for
    * which condition (1) is satisfied; cands contains those views
    * corresponding to conditions (2) and (3).  The list is sorted (wrt
    * ComponentView.compare).  */
  import MissingCommon.MissingCandidates // List[ComponentView]

  /** When any element of missingCandidates is satisfied, then this obligation
    * will be discharged.  Each MissingCandidates within the list is sorted
    * (wrt ComponentView.compare). */
  private var missingCandidates = List[MissingCandidates]()
  /* We maintain the invariant that, if this is the first non-done MissingCommon
   * in a MissingInfo, then the first element of each list is either missing
   * from the current view set, or in the set of new views being considered on
   * the current ply.  The MissingInfo object containing this object will be
   * registered against those first elements in the EffectOnStore. */

  /** Is this constraint satisfied? */
  private var isDone = false

  /** Is this constraint satisfied? */
  @inline def done = isDone

  // Log for debugging

  import MissingCommon.{MCEvent,AddMC,UpdateMC,SetDoneMC}
  private var theLog = List[MCEvent]() 

  /** Logging for debugging.  Currently turned off. */
  def log(e: MCEvent) = {} // theLog ::= e

  /** Record that this is now done.  Also clear missingCandidates to reclaim
    * memory. */
  private def setDone = { 
    isDone = true; missingCandidates = List(); log(SetDoneMC) 
  }

  /** The heads of the missing candidates.  The corresponding MissingInfo should
    * be registered against these in
    * EffectOnStore.mcMissingCandidatesStore. */
  def missingHeads = missingCandidates.map(_.head)

  import MissingCommon.ViewBuffer // ArrayBuffer[ComponentView]

  /** Remove the maximum prefix of mc consisting of elements of views.  If any
    * is empty, record that this is done; otherwise add the next view to
    * toRegister. */
  @inline private def removeViews(mc: MissingCandidates, views: ViewSet,
    toRegister: ViewBuffer)
      : MissingCandidates = {
    var mc1 = mc
    while(mc1.nonEmpty && views.contains(mc1.head)) mc1 = mc1.tail
    if(mc1.isEmpty) setDone    // This is now satisfied
    else toRegister += mc1.head
    log(UpdateMC(mc, mc1))
    mc1
  }


  /** Update missingCandidates based on views.  Remove elements of views from
    * the front of each.  If any is now empty, then mark this as satisfied.
    * Return views against which this should now be registered, or null if
    * done. */
  def updateMissingViews(views: ViewSet): ArrayBuffer[ComponentView] = {
    if(done){ assert(missingCandidates.isEmpty);  null } 
    else{
      val toRegister = new ArrayBuffer[ComponentView]
      assert(missingCandidates.nonEmpty)
      val newMC = missingCandidates.map(mc => removeViews(mc, views, toRegister))
      if(done){ assert(missingCandidates.isEmpty);  null }
      else{
        missingCandidates = newMC
        assert(toRegister.nonEmpty,
          s"updateMissingViews with\n${missingCandidates}")
        toRegister
      }
    }
  }

  /** Is cv a possible match to clause (1), i.e. does it match servers ||
    * cpts1(0) || c? */
  @inline def matches(cv: ComponentView) = 
    cv.servers == servers && cv.components(0) == princ1
  // IMPROVE: can we also ensure that cv.components(1).processIdentity == pid?

  /** Update this based on using cv to instantiate servers || princ1 || c.  Add
    * to vb those Views against which this needs to be registered, namely
    * missingHeads. */
  def updateWithNewMatch(cv: ComponentView, views: ViewSet, vb: ViewBuffer) = {
    assert(!done)
    require(matches(cv)); val cpt1 = cv.components(1) 
    if(cpt1.hasPID(pid))
      if(MissingCommon.updateMissingCandidates(this, cpt1, views, vb))
        setDone
  }

  /** States for which MissingCommon.updateMissingCandidates has been executed
    * on this. */
  private val doneMissingCandidates = new HashSet[State]
    // new HashMap[State,List[State]]

  /** Called by MissingCommon.updateMissingCandidates when updating this with
    * st.  Return true if this is the first such instance for st. */
  private def isNewUMCState(st: State): Boolean = doneMissingCandidates.add(st)

  /** States for which the loop of MissingCommon.updateMissingCandidates has
    * been executed, i.e. states instantiating c there. */
  private val doneMissingCandidatesRenamed: HashSet[State] = null
  // new HashSet[State]  IMPROVE: not used at present

  /** Called by MissingCommon.updateMissingCandidates when updating this with
    * st.  Return true if this is the first such instance for st instantiating
    * c. */
  private def isNewUMCRenamedState(st: State): Boolean = 
    doneMissingCandidatesRenamed.add(st)

  import MissingCommon.{Eq,Sub,Sup,Inc}

  /** Add mCand to missingCandidates if no subset is there already; remove any
    * superset of mCand.  Return true if successful.  Pre: mCand is
    * sorted.  */
  private def add(mCand: MissingCandidates): Boolean = {
    assert(!done)
    require(isSorted(mCand), mCand) // IMPROVE: quite expensive
    // Traverse missingCandidates.  Add to newMC any that is not a proper
    // superset of mCand.
    var newMC = List[MissingCandidates]()
    var found = false // true if missingCandidates includes a subset of mCand
    for(mCand1 <- missingCandidates){
      val cmp = MissingCommon.compare(mCand1, mCand)
      if(cmp != Sup) newMC::= mCand1 // mCand1 can't be replaced by mCand
      found ||= cmp == Sub || cmp == Eq // mCand can't be replaced by mCand1
    }
    if(!found){ newMC ::= mCand; log(AddMC(mCand)) } 
    assert(newMC.nonEmpty)
    missingCandidates = newMC
    !found
  }

  /** Is mCand sorted, without repetitions. */
  private def isSorted(mCand: MissingCandidates): Boolean = 
    mCand.length < 2 || 
      mCand.head.compare(mCand.tail.head) < 0 && isSorted(mCand.tail)

  /** Sanity check that no head element of missingCandidates is in views. */
  def sanityCheck(views: ViewSet) = {
    // assert(!done) -- might not be true as MissingCommons are shared
    if(done) assert(missingCandidates.isEmpty, 
      s"missingCandidates = \n"+missingCandidates.mkString("\n"))
    else for(mcs <- missingCandidates){
      val v = mcs.head
      assert(!views.contains(v), s"\n$this\n  still contains $v")
    }
  }

  override def toString = 
    s"MissingCommon($servers, ${StateArray.show(cpts1)},\n"+
      s"  ${StateArray.show(cpts2)}, $pid)\n"+
      s"  missingCandidates = \n    "+missingCandidates.mkString("\n    ")+
      s"\ndone = $done; theLog = \n"+theLog.reverse.mkString("\n")

  /* Note: we avoid creating duplicates of MissingCommon objects, so we can use
   * object equality. */

/*
  /** Equality test.  The constraint this represents is logically captured by
    * its initial parameters, so we use equality of parameters as the notion
    * of equality. */
// IMPROVE: we avoid creating duplicates, so we could use reference equality
  override def equals(that: Any) = that match{
    case mc: MissingCommon => 
      mc.hashCode == hashCode && // optimisation
      mc.servers == servers && mc.cpts1.sameElements(cpts1) &&
      mc.cpts2.sameElements(cpts2) && mc.pid == pid
    case null => false
  }
 */

/*
  /** Hash code, based on the same principle as equality. */
  override val hashCode = {
    @inline def f(x:Int, y: Int) = x*97+y
    f(f(f(f(servers.hashCode, StateArray.mkHash(cpts1)), 
      StateArray.mkHash(cpts2)), pid._1), pid._2)
  }
 */

  /** Ordering on MissingCommon values.  Return a value x s.t.: x < 0 if this <
    * that; x == 0 when this == that; x > 0 when this > that. */
  def compare(that: MissingCommon) = {
    /* The following makes comparison more efficient, but makes the ordering
     * nondeterministic (varying from one run to another), and so makes the
     * final sizes of the stores nondeterministic.
    val hashComp = compareHash(hashCode, that.hashCode)
    if(hashComp != 0) hashComp
    else{ */
    val ssComp = servers.compare(that.servers)
    if(ssComp != 0) ssComp
    else{
      val cmp1 = StateArray.compare(cpts1, that.cpts1)
      if(cmp1 != 0) cmp1
      else{
        val cmp2 = StateArray.compare(cpts2, that.cpts2)
        if(cmp2 != 0) cmp2
        else{
          val familyDiff = pid._1 - that.pid._1
          if(familyDiff != 0) familyDiff
          else pid._2 - that.pid._2
        }
      }
    }
  }

  /** Has this been counted for profiling purposes? */
  private var counted = false

  /** A measure of the size of this: the number of ComponentViews stored.  If
    * size has already been called, then return 0 to avoid double-counting. */
  def size = {
    if(counted) 0
    else{
      counted = true; var mcs = missingCandidates; var size = 0
      while(mcs.nonEmpty){ size += mcs.head.length; mcs = mcs.tail }
      size
    }
  }
}


// =======================================================

object MissingCommon{
  /* Overview of main functions.
   * 
   * makeMissingCommon          (called from EffectOn)
   * |--updateMissingCandidates  (also called from companion updateWithNewMatch)
   *   |--Unification.remapToJoin
   *   |--getMissingCandidates
   * 
   * Profiling, 2021/10/22, ~10% of total Checker time is spent within
   * makeMissingCommon.
   */

  /** A buffer for storing Views, against which a MissingInfo should be
    * registered in the EffectOnStore. */
  type ViewBuffer = ArrayBuffer[ComponentView]

  /** All the MissingCommon we have created.  */
  private var allMCs = 
    new HashMap[(ServerStates, List[State], ProcessIdentity), MissingCommon]

  /** Get a MissingCommon corresponding to servers, cpts1, cpts2, pid: either
    * retrieving a previous such object, or creating a new one.  The
    * MissingCommon is paired with a Boolean that indicates if it is new. */
  @inline private def getOrInit(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State],
    pid: ProcessIdentity)
      : (MissingCommon, Boolean) = { 
    val key = (servers, cpts1.toList++cpts2.toList, pid)
    allMCs.get(key) match{
      case Some(mc) => Profiler.count("old MissingCommon"); (mc, false)
      case None => 
        val mc = new MissingCommon(servers, cpts1, cpts2, pid)
        Profiler.count("new MissingCommon"); allMCs += key -> mc; (mc, true)
    }
  }

  /** Reset ready for a new check. */
  def reset = 
    allMCs = 
      new HashMap[(ServerStates, List[State], ProcessIdentity), MissingCommon]

  /** A MissingCommon object, corresponding to servers, cpts1, cpts2 and pid, or
    * null if the obligation is already satisfied.
    * 
    * For each component state c with identity pid such that servers ||
    * cpts1(0) || c is in views, missingCandidates contains the list of Views
    * that are needed to satisfy the obligation but are currently missing from
    * views: (1) servers || cpts2(0) || c; and (2) if c has a reference to a
    * secondary component c2 of cpts1 or cpts2, then servers || c || c2
    * (renamed).
    */
  def makeMissingCommon(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State], 
    pid: ProcessIdentity, views: ViewSet)
      : MissingCommon = {
    Profiler.count("makeMissingCommon")
    assert(singleRef)
    assert(cpts2.length == 2, StateArray.show(cpts2))
    val (mc, isNew) = getOrInit(servers, cpts1, cpts2, pid)
    if(isNew){ 
      // Initialise mc, based on views
      val ab = new ViewBuffer
      val princ1 = cpts1(0); val princ2 = cpts2(0); var found = false
      // Search for elements of views of the form servers || princ1 || c where c
      // has identity pid
      val iter = views.iterator(servers, princ1)
      while(iter.hasNext && !found){
        val cv = iter.next; val cpts = cv.components; 
        assert(cpts.length == 2, cv); val cpt1 = cpts(1)
        if(cpt1.hasPID(pid)) found = updateMissingCandidates(mc, cpt1, views, ab)
      }
      if(found){ mc.setDone; null } else mc 
      // Note: we don't need to do anything with ab here, as mc.allcandidates
      // will store the same Views.  IMPROVE?
    }
    else if(mc.done) null else mc 
  }

  /** Update mc.missingCandidates to include lists of missing views
    * corresponding to instantiating c with a renaming of cpt1.  Add to vb the
    * views that mc needs to be registered against in the EffectOnStore,
    * namely mc.missingHeads.
    * 
    * Pre: views contains a view mc.servers || mc.cpts1(0) || cpt1 to
    * instantiate clause (1) of mc.
    * 
    * @return true if mc is now complete. */
  @inline private 
  def updateMissingCandidates(
    mc: MissingCommon, cpt1: State, views: ViewSet, vb: ViewBuffer)
      : Boolean = {
    assert(!mc.done)
    require(cpt1.hasPID(mc.pid))
    if(mc.isNewUMCState(cpt1)){
      // All relevant renamings of cpt1: identity on params of servers and
      // princ1, but otherwise either to other params of cpts2 or to fresh
      // values.
// FIXME: also rename to other params of cpts1?
      val renames = 
        Unification.remapToJoin(mc.servers, mc.princ1, mc.cpts2, cpt1)
      var i = 0; var found = false
      while(i < renames.length && !found){
        val c = renames(i); i += 1
        if(true || mc.isNewUMCRenamedState(c)){ // IMPROVE
          val missing = getMissingCandidates(mc, c, views)
          if(missing.isEmpty) found = true
          else{
            // Note we have to register the corresponding MissingInfo against
            // missing.head, whether or not the add succeeded, because this
            // might be shared between MissingInfos.
            mc.add(missing); vb += missing.head
          }
        }
      } // end of while loop
      found
    }
    else{ 
      // This update has previously been done, but we might need to
      // re-register the MissingInfo object, because of sharing.  The
      // following might be a bit pessimistic.  IMPROVE: store the relevant
      // values from one instance to reuse in the next.
      for(cv <- mc.missingHeads) if(!views.contains(cv)) vb += cv
      false
    }
  }

  /** Find the missing Views that are necessary to complete mc for a particular
    * candidate state c.  Return a list containing each of the following that
    * is not currently in views: (1) mc.servers || mc.cpts2(0) || c; and (2)
    * if c has a reference to a secondary component c2 of mc.cpts1 or
    * mc.cpts2, then mc.servers || c || c2 (renamed).  The list is sorted (wrt
    * ComponentView.compare).  */
  @inline private 
  def getMissingCandidates(mc: MissingCommon, c: State, views: ViewSet)
      : List[ComponentView] = {
    var missing = List[ComponentView]() // missing necessary views
    val servers = mc.servers; val cpts1 = mc.cpts1; val cpts2 = mc.cpts2
    // Add servers || cptsx, if not in views
    @inline def maybeAdd(cptsx: Array[State]) = { 
      val cvx = Remapper.mkComponentView(servers, cptsx)
      if(!views.contains(cvx) && !missing.contains(cvx)) missing ::= cvx
      // IMPROVE: insert so as to maintain sorted order. 
    }

    maybeAdd(Array(cpts2(0), c))
    // If c has a reference to a secondary component c2 of cpts2 or cpts1,
    // then the View servers || c || c2 is necessary.  This avoids a false
    // error with lockFreeQueue.csp.
    var j = 1
    while(j < c.length){
      if(c.includeParam(j)){
        val pid2 = c.processIdentities(j)
        val c2 = StateArray.find(pid2, cpts2)
        if(c2 != null) maybeAdd(Array(c, c2))
        val c1 = StateArray.find(pid2, cpts1)
        if(c1 != null) maybeAdd(Array(c, c1))
      }
      j += 1
    }
    missing.sortWith(ComponentView.compare _)
  }

  // Possible returns from compare
  private val Eq = 0; private val Sub = 1; 
  private val Sup = 2; private val Inc = 4

  /** Each value cands of type MissingCandidates represents that if all the
    * elements of cands are added to the ViewSet, then this obligation will be
    * discharged.  Each corresponds to a particular component state c for
    * which condition (1) is satisfied; cands contains those views
    * corresponding to conditions (2) and (3).  The list is sorted (wrt
    * ComponentView.compare).  */
  type MissingCandidates = List[ComponentView]

  /** Compare mc1 and mc2.  Return Eq is equal, Sub if mc1 is proper subset, Sup
    * if mc1 is a proper superset, and Inc if they are incomparable.  Pre:
    * both are sorted.  */
  @inline private 
  def compare(mc1: MissingCandidates, mc2: MissingCandidates): Int = {
    var c1 = mc1; var c2 = mc2; var sub = true; var sup = true
    // Inv sub is true if elements of mc1 seen so far are all in mc2; sup is
    // true if elements of mc2 seen so far are all in mc1.  Still need to
    // compare c1 and c2.
    while(c1.nonEmpty && c2.nonEmpty && (sub || sup)){
      val comp = c1.head.compare(c2.head)
      if(comp < 0){ sub = false; c1 = c1.tail } // c1.head not in mc2
      else if(comp == 0){ c1 = c1.tail; c2 = c2.tail }
      else{ sup = false; c2 = c2.tail } // c2.head is not in mc1
    }
    sub &&= c1.isEmpty; sup &&= c2.isEmpty
    if(sub){ if(sup) Eq else Sub } else if(sup) Sup else Inc
  }

  // Events for log 
  trait MCEvent
  case class AddMC(mc: MissingCandidates) extends MCEvent 
  case class UpdateMC(mc: MissingCandidates, mc1: MissingCandidates)
      extends MCEvent
  case object SetDoneMC extends MCEvent
}
