package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet,HashMap,Set}
import MissingCommon.Cpts // = Array[State]

/** The representation of the obligation to find a component state c with
  * identity pid such that (1) servers || cpts1(0) || c is in the ViewSet; (2)
  * servers || cpts2(0) || c is in the ViewSet; (3) if c has a reference to a
  * secondary component c2 of cpts1 or cpts2, then servers || c || c2 is in
  * ViewSet (modulo renaming).  This corresponds to condition (c) in the
  * definition of induced transitions with restricted views. */
class MissingCommon(
    val servers: ServerStates, val cpts1: Cpts, val cpts2: Cpts,
    val pid: ProcessIdentity){
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

  private val princ1 = cpts1(0)

  /** Highlight if this relates to the relevant instance. 
    * servers = [107(N0) || 109(N1) || 110() || 114(T0) || 119() || 1()]
    * cpts1 = [75(T0,N0,N1,N2) || 14(N0,N1,Null)]
    * cpts2 = [31(T1,N3,N2,N1) || 10(N3,Null,N2)] */
  private def highlight = 
    (pid == (0,1) || pid == (0,2)) && Transition.highlightPreServers(servers) && 
    Transition.highlightPreCpts(cpts1) && {
      val princ2 = cpts2(0)
      princ2.cs == 31 && princ2.ids.sameElements(Array(1,3,2,1)) && {
        val second2 = cpts2(1)
        second2.cs == 10 && second2.ids.sameElements(Array(3,-1,2))
      }
    }

  require(princ1.processIdentities.contains(pid) && 
    cpts2(0).processIdentities.contains(pid))

  /** Each value cands of type MissingComponents represents that if
    * (servers,cpts) is added to the ViewSet for each cpts in cands, then this
    * obligation will be discharged.  Each corresponds to a particular
    * component state c for which condition (1) is satisfied; cands contains
    * those components corresponding to conditions (2) and (3).  Each such
    * cands is sorted (wrt StateArray.lessThan).  */
  import MissingCommon.MissingComponents // = Array[Array[State]]

  def showMissingComponents(cptsList: MissingComponents) =
    cptsList.map(StateArray.show).mkString("; ")

  /** When any element of missingCandidates is satisfied, then this obligation
    * will be discharged.  Each MissingComponents within the list is sorted
    * (wrt StateArray.lessThan). */
  private[this] var missingCandidates = List[MissingComponents]()
  /* We maintain the invariant that, if this is the first non-done MissingCommon
   * in a MissingInfo, then the first element of each list is either missing
   * from the current view set, or in the set of new views being considered on
   * the current ply.  The MissingInfo object containing this object will be
   * registered against those first elements in the EffectOnStore. */

  /** Is this constraint satisfied? */
  private var isDone = false

  /** Is this constraint satisfied? */
  @inline def done = synchronized{ isDone }

  // Log for debugging
  import MissingCommon.{MCEvent, AddMC, UpdateMC, SetDoneMC,
    MissingCandidateSuccess, UMCRepeat}
  // private var theLog = List[MCEvent]() 

  /** Logging for debugging.  Currently turned on. */
  def log(e: MCEvent) = {} 
  // def log(e: MCEvent) = synchronized{ theLog ::= e }

  /** Record that this is now done.  Also clear missingCandidates and
    * doneMissingCandidates to reclaim memory. */
  private def setDone = { 
    isDone = true; missingCandidates = List(); doneMissingCandidates = null
    log(SetDoneMC)
  }

  def notDoneEmpty = !isDone && missingCandidates.isEmpty

  /** The heads of the missing candidates.  The corresponding MissingInfo should
    * be registered against these in EffectOnStore.mcNotDoneStore. */
  def missingHeads: List[Cpts] = synchronized{ missingCandidates.map(_(0)) }

  import MissingCommon.CptsBuffer // = ArrayBuffer[Array[State]]

  /** Remove the maximum prefix of mc consisting of elements of views.  If any
    * is empty, record that this is done; otherwise add the next view to
    * toRegister. */
  @inline private 
  def removeViews(mc: MissingComponents, views: ViewSet, toRegister: CptsBuffer)
      : MissingComponents = {
    // For simplicity, we convert to a List, and back to an Array at the end.
    // This could be improved.
    var mc1 = mc.toList
    while(mc1.nonEmpty && views.contains(servers, mc1.head)) mc1 = mc1.tail
    log(UpdateMC(mc, mc1.toArray, ply))
    if(mc1.isEmpty) setDone    // This is now satisfied
    else toRegister += mc1.head
    mc1.toArray
  }

  /** Update missingCandidates based on views.  Remove elements of views from
    * the front of each.  If any is now empty, then mark this as satisfied.
    * Return views against which this should now be registered, or null if
    * done. */
  def updateMissingViews(views: ViewSet): CptsBuffer = synchronized{
    // if(highlight) println(s"updateMissingViews $pid "+
    //   missingCandidates.map(showMissingComponents))
    if(done){ assert(missingCandidates.isEmpty); null } 
    else{
      val toRegister = new CptsBuffer
      // Note: it's possible that missingCandidates is empty here
      val newMC = missingCandidates.map(mc => removeViews(mc, views, toRegister))
      // if(highlight){
      //   if(done) println("Now done")
      //   else println("newMC = "+newMC.map(showMissingComponents _))
      // }
      if(done){ assert(missingCandidates.isEmpty);  null }
      else{
        missingCandidates = newMC
        assert(missingCandidates.isEmpty || toRegister.nonEmpty, 
          s"updateMissingViews with\n${missingCandidates}")
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
    if(highlight) println(s"updateWithNewMatch($cv) $pid")
    if(!done){
      val cpt1 = cv.components(1)
      val vb = new CptsBuffer
      if(cpt1.hasPID(pid)){
        if(updateMissingCandidates(cpt1, views, vb)){ 
          log(MissingCommon.UpdateWithNewMatchSuccess(cv, ply))
          if(highlight) println("Now done")
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
  @inline private 
  def updateMissingCandidates(cpt1: State, views: ViewSet, vb: CptsBuffer)
      : Boolean = {
    if(highlight) println(s"updateMissingCandidates($cpt1) $pid")
    require(!done && cpt1.hasPID(pid))
    if(isNewUMCState(cpt1)){
      // All relevant renamings of cpt1: identity on params of servers and
      // princ1, but otherwise either to other params of cpts2 or to fresh
      // values.
// FIXME: also rename to other params of cpts1?
      val renames = Unification.remapToJoin(servers, princ1, cpts2, cpt1)
      var i = 0; var found = false
      while(i < renames.length && !found){
        val c = renames(i); i += 1
        // if(highlight) println(s"c = $c")
        if(true || isNewUMCRenamedState(c)){ // IMPROVE
          val missing = getMissingCandidates(c, views)
          // if(highlight){
          //   if(missing.isEmpty) println("found") 
          //   else println("missing = "+showMissingComponents(missing))
          // }
          if(missing.isEmpty){ 
            log(MissingCandidateSuccess(cpt1, c)); found = true 
          }
          else{
            // Note we have to register the corresponding MissingInfo against
            // missing.head, whether or not the add succeeded, because this
            // might be shared between MissingInfos.
            add(missing); vb += missing.head 
          }
        }
      } // end of while loop
      // if(highlight && !found) println(s"found = $found; missingComponents = "+
      //   missingCandidates.map(showMissingComponents))
      //if(highlight) println(s"found = $found")
      found
    } // end of if isNewUMCState
    else{ 
      // This update has previously been done, but we might need to
      // re-register the MissingInfo object, because of sharing.  The
      // following might be a bit pessimistic.  IMPROVE: store the relevant
      // values from one instance to reuse in the next.
      log(UMCRepeat(cpt1))
// FIXME: I think the commented-out code is better, but needs to deal with the
// case that vb1 is null.  
/*
      val vb1 = updateMissingViews(views); assert(vb1 != null, this)
      vb ++= vb1 
 */
      for(cpts <- missingHeads) 
        if(true || !views.contains(servers, cpts)) vb += cpts
      false
    }
  }

  /** Find the missing components that (with servers) are necessary to complete
    * this for a particular candidate state c.  Return a list containing each
    * of the following that is not currently in views: (1) cpts2(0) || c; and
    * (2) if c has a reference to a secondary component c2 of cpts1 or cpts2,
    * then c || c2 (renamed).  The list is sorted (wrt
    * StateArray.lessThan).  */
  @inline private 
  def getMissingCandidates(c: State, views: ViewSet): MissingComponents = {
    //if(highlight) println(s"getMissingCandidates($c)")
    var missing = List[Array[State]]() // missing necessary views
    //val servers = mc.servers; val cpts1 = mc.cpts1; val cpts2 = mc.cpts2
    // Add cptsx, if servers || cptsx is not in views
    @inline def maybeAdd(cptsx: Array[State]) = { 
      val renamedCpts = Remapper.remapComponents(servers, cptsx)
      //if(highlight) println(s"renamedCpts = "+StateArray.show(renamedCpts))
      if(!views.contains(servers, renamedCpts) && 
          !missing.exists(_.sameElements(renamedCpts)))
        missing ::= renamedCpts
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
    missing.toArray.sortWith(StateArray.lessThan)
  }

  /** States for which MissingCommon.updateMissingCandidates has been executed
    * on this. */
  private var doneMissingCandidates = Set[State]() // new HashSet[State]

  /** Called by MissingCommon.updateMissingCandidates when updating this with
    * st.  Return true if this is the first such instance for st. */
  private def isNewUMCState(st: State): Boolean = doneMissingCandidates.add(st)

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

  /** Add mCand to missingCandidates if no subset is there already; remove any
    * superset of mCand.  Return true if successful.  Pre: mCand is
    * sorted.  */
  private def add(mCpts: MissingComponents): Boolean = {
    assert(!done)
    require(isSorted(mCpts), mCpts.map(StateArray.show)) // IMPROVE: quite expensive
    // Traverse missingCandidates.  Add to newMC any that is not a proper
    // superset of mCpts.
    var newMC = List[MissingComponents]()
    var found = false // true if missingCandidates includes a subset of mCpts
    for(mCpts1 <- missingCandidates){
      // Note: mCpts is local; this is locked; so neither of following
      // parameters can be mutated by a concurrent thread.
      val cmp = MissingCommon.compare(mCpts1, mCpts)
      if(cmp != Sup) newMC::= mCpts1 // mCpts1 can't be replaced by mCpts
      found ||= cmp == Sub || cmp == Eq // mCpts can't be replaced by mCpts1
    }
    if(!found){ newMC ::= mCpts; log(AddMC(mCpts)) } 
    assert(newMC.nonEmpty)
    missingCandidates = newMC
    !found
  }

  /** Is mCand sorted, without repetitions. */
  private def isSorted(mCpts: MissingComponents): Boolean = {
    var i = 0
    while(i < mCpts.length-1 && StateArray.compare(mCpts(i), mCpts(i+1)) < 0)
      i += 1
    i == mCpts.length-1
  }
  // mCpts.length < 2 || 
  // StateArray.compare(mCpts.head, mCpts.tail.head) < 0 && isSorted(mCpts.tail)

  /** Sanity check that no head element of missingCandidates is in views. */
  def sanityCheck(views: ViewSet) = {
    // assert(!done) -- might not be true as MissingCommons are shared
    if(done) assert(missingCandidates.isEmpty, 
      s"missingCandidates = \n"+missingCandidates.mkString("\n"))
    else for(mcs <- missingCandidates){
      val v = new ComponentView(servers, mcs.head)
      assert(!views.contains(v), s"\n$this\n  still contains $v")
    }
  }

  override def toString = 
    s"MissingCommon($servers, ${StateArray.show(cpts1)},\n"+
      s"  ${StateArray.show(cpts2)}, $pid)\n"+
      s"  missingCandidates = "+
      missingCandidates.map(showMissingComponents).mkString("\n    ")+
      s"\n  done = $done\n" // theLog = "+theLog.reverse.mkString("\n    ")+"\n"

  /* Note: we avoid creating duplicates of MissingCommon objects, so we can use
   * object equality. */

  /** Ordering on MissingCommon values.  Return a value x s.t.: x < 0 if this <
    * that; x == 0 when this == that; x > 0 when this > that. */
  def compare(that: MissingCommon) = {
    // Note: refers only to parameters, so locking not necessary.
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
   * |--getOrInit
   * |--(companion).updateMissingCandidates 
   */

  /** The states of some components. */
  type Cpts = Array[State]

  /** A buffer for storing Cpts, against which a MissingInfo should be
    * registered in the EffectOnStore (with appropriate servers). */
  type CptsBuffer = ArrayBuffer[Cpts]

  /** Each value cands of type MissingComponents represents that if
    * (servers,cpts) is added to the ViewSet for each cpts in cands, then this
    * obligation will be discharged.  Each corresponds to a particular
    * component state c for which condition (1) is satisfied; cands contains
    * those components corresponding to conditions (2) and (3).  The list is
    * sorted (wrt StateArray.lessThan).  */
  type MissingComponents = Array[Cpts]

  def showMissingComponents(mc: MissingComponents) = 
    mc.map(StateArray.show).mkString("; ")

  /** Type of keys for stored MissingCommons. */
  //private type Key = (ServerStates, List[State], ProcessIdentity)
// IMPROVE: create more memory-efficient type

  /** Type of keys for storing MissingCommons. */
  class Key(
      val ssIndex: Int, val cpts: Array[State], val pf: Int, val pId: Int){
    override def hashCode = StateArray.mkHash((ssIndex*71+pf)*71+pId, cpts)

    override def equals(that: Any) = that match{
      case key: Key => 
        key.ssIndex == ssIndex && key.pf == pf && key.pId == pId &&
        key.cpts.sameElements(cpts)
    }
  }

  private def mkKey(
    servers: ServerStates, cpts1: Cpts, cpts2: Cpts, pid: ProcessIdentity)
      : Key = {
    // Build concatenation of cpts1 and cpts2
    val cpts = new Array[State](cpts1.length+cpts2.length)
    var i = 0; var j = 0
    while(i < cpts1.length){ cpts(j) = cpts1(i); i += 1; j += 1 }
    i = 0
    while(i < cpts2.length){ cpts(j) = cpts2(i); i += 1; j += 1 }
    new Key(servers.index, cpts, pid._1, pid._2)
  }

  /** The type of the store of all MissingCommon we have created. */
  //type MissingCommonStore = MyLockFreeReadHashMap[Key, MissingCommon]
  type MissingCommonStore = ShardedHashMap[Key, MissingCommon]

  /** All the MissingCommon we have created.  Protected by a synchronized block
    * on itself.*/
  private var allMCs = new MissingCommonStore 

  /** Get the MissingCommon associated with key. */
  @inline private def getMC(key: Key) = allMCs.get(key)
  // allMCs.synchronized{ allMCs.get(key) }

  /** Store mc against key, unless there is already an associated value.  Return
    * the resulting stored value. */
  private def setOrGet(key: Key, mc: MissingCommon) = /*allMCs.synchronized*/{
    allMCs.getOrElseUpdate(key, mc)
  }

  private var shardIteratorProducer: 
       ShardedHashMap.ShardIteratorProducerT[Key, MissingCommon] = null

  def prepareForPurge = { shardIteratorProducer = allMCs.shardIteratorProducer }

  /** Purge MissingCommons that are done. */
  def purgeMCs() = { 
    var shardIterator = shardIteratorProducer.get
    while(shardIterator != null){
      // for((key,mc) <- shardIterator){
      while(shardIterator.hasNext){
        val (key,mc) = shardIterator.next()
        if(mc.done) allMCs.remove(key)
      }
      shardIterator = shardIteratorProducer.get
    }
  }

  def allMCsSize = allMCs.size

  /** Perform a memory profile of this. */
  def memoryProfile = {
    import ox.gavin.profiling.MemoryProfiler.traverse
    println("MissingCommon.allMCs size = "+allMCs.size)
/* IMPROVE: needs take on map
    for(mc <- allMCs.take(3)){
      traverse("missingCommon", mc, maxPrint = 2); println()
    }
 */
    traverse("allMCs", allMCs, maxPrint = 1); println()
    traverse("MissingCommon", this, maxPrint = 1); println()
  }

  // /** Get a MissingCommon corresponding to servers, cpts1, cpts2, pid: either
  //   * retrieving a previous such object, or creating a new one.  The
  //   * MissingCommon is paired with a Boolean that indicates if it is new. */
  // @inline private def getOrInit(
  //   servers: ServerStates, cpts1: Cpts, cpts2: Cpts, pid: ProcessIdentity)
  //     : (MissingCommon, Boolean) = { 
  //   val key = (servers, cpts1.toList++cpts2.toList, pid)
  //   allMCs.get(key) match{
  //     case Some(mc) => Profiler.count("old MissingCommon"); (mc, false)
  //     case None => 
  //       val mc = new MissingCommon(servers, cpts1, cpts2, pid)
  //       Profiler.count("new MissingCommon"); allMCs += key -> mc; (mc, true)
  //   }
  // }

  /** Reset ready for a new check. */
  def reset = 
    allMCs = new MissingCommonStore // MyLockFreeReadHashMap[Key, MissingCommon]

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
    servers: ServerStates, cpts1: Cpts, cpts2: Cpts, 
    pid: ProcessIdentity, views: ViewSet)
      : MissingCommon = {
    require(singleRef && cpts2.length == 2, StateArray.show(cpts2))
    // val key = (servers, cpts1.toList++cpts2.toList, pid)
    val key = mkKey(servers, cpts1, cpts2, pid)
    getMC(key) match{
      case Some(mc) => 
        Profiler.count("old MissingCommon")
        if(mc.done) null else mc 
      case None => 
        val mc = new MissingCommon(servers, cpts1, cpts2, pid)
        Profiler.count("new MissingCommon")
        val ab = new CptsBuffer
        val princ1 = cpts1(0); val princ2 = cpts2(0); var found = false
        // Search for elements of views of the form servers || princ1 || c
        // where c has identity pid
        val iter = views.iterator(servers, princ1)
        while(iter.hasNext && !found){
          val cv = iter.next(); val cpts = cv.components;
          assert(cpts.length == 2, cv); val cpt1 = cpts(1)
          if(cpt1.hasPID(pid))
            found = mc.updateMissingCandidates(cpt1, views, ab)
        }
        if(found) mc.setDone
        // if(mc.notDoneEmpty){
        //   println(s"$mc is not done but has empty missing candidates.")
        //   println("iter = "+views.iterator(servers, princ1).mkString("\n"))
        //   sys.exit()
        // }
        // Store mc if no other thread has done likewise in the meantime
        val mc2 = setOrGet(key, mc)
        if(!(mc2 eq mc)){
          println("Creation of MissingCommon duplicated.");
          Profiler.count("duplicate MissingCommon")
        }
        if(mc2.done) null else mc2
    }
  }

// // IMPROVE: we wrap this in a synchronized block, to protect allMCs; but I
// // suspect we can do better.  Need to ensure the MissingCommon is fully
// // initiailised before it becomes visible.
//     Profiler.count("makeMissingCommon")
//     assert(singleRef)
//     assert(cpts2.length == 2, StateArray.show(cpts2))
//     val (mc, isNew) = getOrInit(servers, cpts1, cpts2, pid)
//     if(isNew){ 
//       // Initialise mc, based on views
//       val ab = new CptsBuffer
//       val princ1 = cpts1(0); val princ2 = cpts2(0); var found = false
//       // Search for elements of views of the form servers || princ1 || c where c
//       // has identity pid
//       val iter = views.iterator(servers, princ1)
//       while(iter.hasNext && !found){
//         val cv = iter.next(); val cpts = cv.components; 
//         assert(cpts.length == 2, cv); val cpt1 = cpts(1)
//         if(cpt1.hasPID(pid)) 
//           found = mc.updateMissingCandidates(cpt1, views, ab)
//       }
//       if(found){ mc.setDone; null } else mc 
//       // Note: we don't need to do anything with ab here, as mc.allcandidates
//       // will store the same Views.  IMPROVE?
//     }
//     else if(mc.done) null else mc 
//   }

  // Possible returns from compare
  private val Eq = 0; private val Sub = 1; 
  private val Sup = 2; private val Inc = 4

  /** Compare mc1 and mc2.  Return Eq is equal, Sub if mc1 is proper subset, Sup
    * if mc1 is a proper superset, and Inc if they are incomparable.  Pre:
    * both are sorted.  Requires that neither is mutated concurrently. */
  @inline private 
  def compare(mc1: MissingComponents, mc2: MissingComponents): Int = {
    var i1 = 0; var i2 = 0; var sub = true; var sup = true
    // Inv sub is true if elements of mc1 seen so far are all in mc2; sup is
    // true if elements of mc2 seen so far are all in mc1.  Still need to
    // compare from indices i1 and i2 onwards.
    while(i1 < mc1.length && i2 < mc2.length && (sub || sup)){
      val comp = StateArray.compare(mc1(i1), mc2(i2))
      if(comp < 0){ sub = false; i1 += 1 } // c1.head not in mc2
      else if(comp == 0){ i1 += 1; i2 += 1 }
      else{ sup = false; i2 += 1 } // c2.head is not in mc1
    }
    sub &&= (i1 == mc1.length); sup &&= (i2 == mc2.length)
    if(sub){ if(sup) Eq else Sub } else if(sup) Sup else Inc
  }

  // Events for log 
  trait MCEvent
  /** A call to add, leading to missingComponents being set to mc. */
  case class AddMC(mc: MissingComponents) extends MCEvent{
    override def toString = "AddMC"+showMissingComponents(mc)+")"
  }
  /** A call to removeViews(mc) giving result mc1. */
  case class UpdateMC(mc: MissingComponents, mc1: MissingComponents, ply: Int)
      extends MCEvent{
    override def toString = 
      "UpdateMC(mc = "+showMissingComponents(mc)+
        "; mc1 = "+showMissingComponents(mc1)+s"; ply = $ply)"
  }
  /** A call to setDone. */
  case object SetDoneMC extends MCEvent

  /** A call to updateMissingCandidates(cpt1), where instantiating with c led to
    * this becoming done. */
  case class MissingCandidateSuccess(cpt1: State, c: State) extends MCEvent

  /** A call to updateWithNewMatch(cv) was successful. */
  case class UpdateWithNewMatchSuccess(cv: ComponentView, ply: Int)
      extends MCEvent

  /** A call to updateWithNewMatch(cv,...,key). */
  case class UpdateWithNewMatch(cv: ComponentView, key: (ServerStates,State)) 
      extends MCEvent

  /** A repeated call to updateMissingCandidates(cpt1). */
  case class UMCRepeat(cpt1: State) extends MCEvent
}
