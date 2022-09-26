package ViewAbstraction

import ViewAbstraction.collection.ShardedHashMap
import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet,HashMap,Set}
import collection.OpenHashSet
import MissingCommon.Cpts // = Array[State]

/** The representation of the obligation to find a component state c with
  * identity pid such that (1) servers || cpts1(0) || c is in the ViewSet; (2)
  * servers || cpts2(0) || c is in the ViewSet; (3) if c has a reference to a
  * secondary component c2 of cpts1 or cpts2, or vice versa, then servers || c
  * || c2 is in ViewSet (modulo renaming).  This corresponds to condition (c)
  * in the definition of induced transitions with restricted views. */
class MissingCommon(
    val servers: ServerStates, val cpts1: Cpts, val cpts2: Cpts,
    val pid: ProcessIdentity){

// IMPROVE
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

  @inline private def princ1 = cpts1(0)

  /** Highlight if this relates to the relevant instance. 
    * servers = [107(N0) || 109(N1) || 110() || 114(T0) || 119() || 1()]
    * cpts1 = [75(T0,N0,N1,N2) || 14(N0,N1,Null)]
    * cpts2 = [31(T1,N3,N2,N1) || 10(N3,Null,N2)] */
  @inline private def highlight = false && 
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
    isDone = true; missingCandidates = null
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
    // For simplicity, we convert to a List, and back to an Array at the end.
    // This could be improved.
    var mc1 = mc.toList
    while(mc1.nonEmpty && views.contains(servers, mc1.head)) mc1 = mc1.tail
    // log(UpdateMC(mc, mc1.toArray, ply))
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
    if(done){ assert(missingCandidates == null); null } 
    else{
      val toRegister = new CptsBuffer
      // Note: it's possible that missingCandidates is empty here
      val newMC = missingCandidates.map(mc => removeViews(mc, views, toRegister))
      // if(highlight){
      //   if(done) println("Now done")
      //   else println("newMC = "+newMC.map(showMissingComponents _))
      // }
      if(done){ assert(missingCandidates == null);  null }
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
        // Remap cpt1 to a normal form
        val cpt1Norm = Remapper.remapWRT(servers, cpts1, cpts2, cpt1) 
        if(updateMissingCandidates(cpt1Norm, views, vb)){ 
          //log(MissingCommon.UpdateWithNewMatchSuccess(cv, ply))
          //if(highlight) println("Now done")
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
    //if(highlight) println(s"updateMissingCandidates($cpt1) $pid")
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
/*    val vb1 = updateMissingViews(views); assert(vb1 != null, this)
      vb ++= vb1  */
      for(cpts <- missingHeads) 
        if(/* true || */ !views.contains(servers, cpts)) vb += cpts
      false
    }
  }

  /** Find the missing components that (with servers) are necessary to complete
    * this for a particular candidate state c.  Return an array containing
    * each of the following that is not currently in views: (1) cpts2(0) || c;
    * and (2) if c has a reference to a secondary component c2 of cpts1 or
    * cpts2, then c || c2 (renamed).  The array is sorted (wrt
    * StateArray.lessThan).  */
  @inline private 
  def getMissingCandidates(c: State, views: ViewSet): MissingComponents = {
    //if(highlight) println(s"getMissingCandidates($c)")
    val missing = new ArrayBuffer[Array[State]] // missing necessary views
    val requiredCpts = MissingCommon.requiredCpts(servers, cpts1, cpts2, c)
    var i = 0
    while(i < requiredCpts.length){
      val cpts = requiredCpts(i); i += 1
//    for(cpts <- MissingCommon.requiredCpts(servers, cpts1, cpts2, c)){
      if(!views.contains(servers, cpts) && !missing.exists(_.sameElements(cpts)))
        missing += cpts
    }
    missing.toArray.sortWith(StateArray.lessThan)
  }

  /** Representation of the States for which
    * MissingCommon.updateMissingCandidates has been executed on this.  State
    * st is represented by st.index+1. */
  private var doneMissingCandidates = new collection.IntSet
    // new scala.collection.mutable.HashSet[Int]
  //  new OpenHashSet[Int](initSize = 4)
// IMPROVE: smaller? 

  /** Called by MissingCommon.updateMissingCandidates when updating this with
    * st.  Return true if this is the first such instance for st. */
  private def isNewUMCState(st: State): Boolean = {
    assert(st.index >= 0)
    doneMissingCandidates.add(st.index+1)
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

  /** Add mCand to missingCandidates if no subset is there already; remove any
    * superset of mCand.  Return true if successful.  Pre: mCand is
    * sorted.  */
  private def add(mCpts: MissingComponents): Boolean = {
    assert(!done)
    // assert(mCpts.forall(cpts => cpts.eq(StateArray(cpts))))

    // require(isSorted(mCpts), mCpts.map(StateArray.show)) // IMPROVE: quite expensive
    // Traverse missingCandidates.  We aim to retain any that is  not a proper
    // superset of mCpts.  Record which to retain in toRetain.
    val toRetain = new Array[Boolean](missingCandidates.length); 
    var i = 0; var retainCount = 0 // number to retain
    var found = false // true if missingCandidates includes a subset of mCpts
    // for(mCpts1 <- missingCandidates){
    // for(i <- 0 until missingCandidates.length){
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
//    for(i <- 0 until missingCandidates.length; if toRetain(i)){
    while(i < missingCandidates.length){
      if(toRetain(i)){ newMC(j) = missingCandidates(i); j += 1 }
      i += 1
    }
    assert(j == retainCount)
    if(!found) newMC(retainCount) = mCpts
    // Profiler.count("MissingCommon.add "+newMC.length)
    missingCandidates = newMC; !found
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
    if(counted || missingCandidates == null) 0
    else{
      counted = true; var i = 0; var size = 0
      while(i < missingCandidates.length){
        size += missingCandidates(i).length; i += 1
      }
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

  /** Type of keys for storing MissingCommons. */
  class Key(
    val ssIndex: Int, val cpts1: Array[State], val cpts2: Array[State],
    val pf: Int, val pId: Int
  ){
    override def hashCode = 
      StateArray.mkHash1( StateArray.mkHash1((ssIndex*71+pf)*71+pId, cpts1), 
        cpts2 )

    override def equals(that: Any) = that match{
      case key: Key => 
        key.ssIndex == ssIndex && key.pf == pf && key.pId == pId &&
        key.cpts1.sameElements(cpts1) && key.cpts2.sameElements(cpts2)
    }
  }

  private def mkKey(
    servers: ServerStates, cpts1: Cpts, cpts2: Cpts, pid: ProcessIdentity) = 
    new Key(servers.index, cpts1, cpts2, pid._1, pid._2)

  /** The type of the store of all MissingCommon we have created. */
  type MissingCommonStore = ShardedHashMap[Key, MissingCommon]

  /** All the MissingCommon we have created.  Protected by a synchronized block
    * on itself.*/
  private var allMCs = new MissingCommonStore 

  /** Get the MissingCommon associated with key. */
  @inline private def getMC(key: Key) = allMCs.get(key)

  /** Store mc against key, unless there is already an associated value.  Return
    * the resulting stored value. */
  private def setOrGet(key: Key, mc: MissingCommon) = {
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
    // Traverse 5 MissingCommons
    val iter = allMCs.valuesIterator
    for(_ <- 0 until 5; if iter.hasNext)
      traverse("MissingCommon", iter.next(), maxPrint = 3); println() 
    // allMCs
    println("MissingCommon.allMCs size = "+allMCs.size)
    traverse("allMCs", allMCs, maxPrint = 1); println()
    // the rest
    traverse("MissingCommon", this, maxPrint = 1); println()
  }

  /** Reset ready for a new check. */
  def reset =  allMCs = new MissingCommonStore

  /** A MissingCommon object, corresponding to servers, cpts1, cpts2 and pid, or
    * null if the obligation is already satisfied.
    * 
    * For each component state c with identity pid such that servers ||
    * cpts1(0) || c is in views, missingCandidates contains the list of Views
    * that are needed to satisfy the obligation but are currently missing from
    * views: (1) servers || cpts2(0) || c; and (2) if c has a reference to a
    * secondary component c2 of cpts1 or cpts2, then servers || c || c2
    * (renamed).
    * 
    * Pre: servers || cpts1 is in normal form.
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
        val ab = new CptsBuffer; val princ1 = cpts1(0); var found = false
        // All component states c with identity pid such that views contains
        // servers || princ1 || c
        val cs = allInstantiations(servers, princ1, pid, views); var i = 0
        // Update mc for each
        while(i < cs.length && !found){
          val c = cs(i); i += 1
          found = mc.updateMissingCandidates(c, views, ab)
        }
        if(found) mc.setDone
        // Store mc if no other thread has done likewise in the meantime
        val mc2 = setOrGet(key, mc)
        if(!(mc2 eq mc)){
          println("Creation of MissingCommon duplicated.");
          Profiler.count("duplicate MissingCommon")
        }
        if(mc2.done) null else mc2
    }
  }

  /** All component states cpt with identity pid such that views contains
    * servers || princ || cpt.  Pre: servers || princ is in normal form. */
  @inline def allInstantiations(
    servers: ServerStates, princ: State, pid: ProcessIdentity, views: ViewSet)
      : ArrayBuffer[State] = {
    val ab = new ArrayBuffer[State]
    val iter = views.iterator(servers, princ)
    while(iter.hasNext){
      val cv = iter.next(); val cpts = cv.components;
      assert(cpts.length == 2, cv); val cpt = cpts(1)
      if(cpt.hasPID(pid)) ab += cpt
    }
    ab
  }

  /** For a MissingCommon corresponding to servers, cpts1 and cpts2, given that
    * c is a component with identity pid that satisfies condition (1), find
    * those components that are required for conditions (2) and (3). */
  @inline def requiredCpts(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State], c: State)
      : ArrayBuffer[Array[State]] = {
    val ab = new ArrayBuffer[Array[State]]
    /* Add the normalised version of cpts to ab. */
    @inline def add(cpts: Array[State]) = {
      ComponentView0.checkValid(servers, cpts) // IMPROVE
      ab += Remapper.remapComponents(servers, cpts)
    }
    // Condition (2)
    add(Array(cpts2(0), c)); var j = 1
    // Condition (3): refs from c to components of cpts1 or cpts2
    while(j < c.length){
      if(c.includeParam(j)){
        val pid2 = c.processIdentities(j)
        val c2 = StateArray.find(pid2, cpts2); if(c2 != null) add(Array(c, c2))
        val c1 = StateArray.find(pid2, cpts1); if(c1 != null) add(Array(c, c1))
      }
      j += 1
    }
    // Note: the following corresponds to references from secondary components
    // of cpts1 or cpts2 to c, which is a new clause in condition (c).
    val (ct,cid) = c.componentProcessIdentity; j = 1
    while(j < cpts1.length){
      val c1 = cpts1(j); j += 1; // if(c1.hasRef(pid)) add(Array(c1, c))
      if(c1.hasIncludedParam(ct, cid)) add(Array(c1, c))
    }
    j = 1
    while(j < cpts2.length){
      val c2 = cpts2(j); j += 1; // if(c2.hasRef(pid)) add(Array(c2, c))
      if(c2.hasIncludedParam(ct, cid)) add(Array(c2, c))
    }
    Profiler.count("MissingCommon.requiredCpts "+ab.length)
    ab
  } 

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
