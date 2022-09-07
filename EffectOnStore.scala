package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashMap,HashSet}

/* Classes in this file record information about when a particular View,
 * newView, can be added, under singleRef.  Each instance arises from a call
 * to EffectOn.apply, but where some views necessary for the compatability of
 * the parameters are not in the ViewSet.  If those required views are
 * subsequently added, we can add newView. */

// =======================================================

/** Objects that record information about which views might be added later.
  * Abstractly it stores a set of MissingInfo objects.
  * 
  * These are added in effectOn when a transition are not yet in the store. */ 
trait EffectOnStore{

  /** Add MissingInfo(nv, missing, missingCommon) to the store. 
    * This corresponds to transition trans inducing
    * cv == (pre.servers, oldCpts) -> (post.servers, newCpts) == newView.*/
  def add(missing: List[ReducedComponentView], 
    missingCommon: List[MissingCommon],
    nv: ComponentView, trans: Transition, oldCpts: Array[State], 
    cv: ComponentView, newCpts: Array[State]): Unit

  /** Try to complete values in the store, based on the addition of cv, and with
    * views as the ViewSet.  Return the Views that can now be added.  */
  def complete(cv: ComponentView, views: ViewSet): ArrayBuffer[ComponentView]

  /** Sanity check performed at the end of a run. */
  def sanityCheck(views: ViewSet): Unit

  /** Purge values from the stores that are not needed. */
  def purgeCandidateForMCStore(views: ViewSet): Unit

  def purgeMCNotDone(views: ViewSet) : Unit

  def purgeMCDone(views: ViewSet) : Unit

  /** Prepare for the next purge. */
  def prepareForPurge: Unit

  def report: Unit

  def memoryProfile: Unit
}

// =======================================================

object EffectOnStore{
  /** Show an induced transition. */
  def showInduced(cv: ComponentView0, oldCpts: Array[State], 
    postServers: ServerStates, newCpts: Array[State], nv: ReducedComponentView)
  = (
    s"$cv\n"+
      (if(!cv.components.sameElements(oldCpts))
        s"  == ${View.show(cv.servers, oldCpts)}\n"
      else "")+
      s"  --> ${View.show(postServers, newCpts)}\n"+
      (if(postServers != nv.servers || !newCpts.sameElements(nv.components))
        s"  ==  $nv"
      else "")
  )
}

// =======================================================

/** A simple implementation of EffectOnStore.  The name "simple" is a
  * misnomer.  */
class SimpleEffectOnStore extends EffectOnStore{
  assert(singleRef)

  /* Overview of main functions.
   * 
   * add
   * |--addToStore
   * 
   * complete
   * |-completeCandidateForMC
   *   |-MissingInfo.{updateMissingCommon, mcDone, done}
   *   |-mcDone
   * |-completeMcNotDone
   *   |-MissingInfo.{updateMissingViewsOfMissingCommon, mcDone, done}
   *   |-mcDone
   * |-completeMcDone
   *   |-MissingInfo.{updateMissingViewsBy, done}
   */

  /** A set of MissingInfos. */
  // type MissingInfoSet =  HashSet[MissingInfo] 
  type MissingInfoSet =  OpenHashSet[MissingInfo]

  @inline def mkMissingInfoSet = 
    new OpenHashSet[MissingInfo](initSize = 8, ThresholdRatio = 0.6F)

  /** A type of stores, giving the MissingInfos that might need updating as the
    * result of finding a new ComponentView. */
  type Store = ShardedHashMap[ReducedComponentView, MissingInfoSet]

  type ViewBuffer = ArrayBuffer[ComponentView]

  /** Information about those mi: MissingInfo in the abstract set such that
    * !mi.mcDone (i.e. not all MissingCommon in mi.missingCommon are done).
    * If mc is the first element of mi.missingCommon that is not done, then
    * for each v in mc.missingHeads, mcNotDoneStore contains v -> mi
    * (i.e. keyed against the next missing view in each option within mc).
    * mcNotDoneStore might also hold some MissingInfos that are mcDone,
    * because they were found to be mcDone in the first phase of complete
    * (from candidateForMCStore). */
  private val mcNotDoneStore = new Store

  /** Information about those mi: MissingInfo in the abstract set such that
    * mi.mcDone (i.e. all MissingCommon in mi.missingCommon are done).  For
    * each such mi, mcDoneStore contains mi.missingHead -> mi (i.e. keyed against
    * the next missing view). */
  private val mcDoneStore = new Store

  /** Information used to identify whether a new view can be used to instantiate
    * c in clause (1) of the obligation of a MissingCommon.  For each mi:
    * MissingInfo in the abstract set, and for each
    * MissingCommon(servers,cpts,_,_) in mi.missingCommon,
    * candidateForMCStore(servers,cpts(0)) contains mi. */
  private val candidateForMCStore = 
    new ShardedHashMap[(ServerStates, State), MissingInfoSet]

  /* Operations on each MissingInfoSet are protected by a synchronized block on
   * that MissingInfoSet.  The protocol for updating a maplet is (1) read the
   * maplet; (2) lock the MissingInfoSet; (3) check the maplet is still valid,
   * and if not restart.  */

/* IMPROVE: periodically purge the stores of MissingInfos that are done or for
 * which the newView has been found, and purge mcNotDoneStore and
 * candidateForMSCStore of MissingInfos that are mcDone. */

  import MissingInfo.{LogEntry,  McNotDoneStore,
    CandidateForMC} // McDoneStore,, NotStored

  /** Do we check with the MissingInfoStore before adding to candidateForMCStore
    * and mcNotDoneStore?  It seems that this doesn't help much. */
  private val MISFlag = false

  /** Does store contain the mapping key -> mis? */
  @inline private def mapsto[A](
    store: ShardedHashMap[A, MissingInfoSet], key: A, mis: MissingInfoSet)
      : Boolean =
    store.get(key) match{
      case Some(mis1) => mis1 eq mis // Note: reference equality
      case None => false
    }

  /** Name of theStore.  Used in logging for debugging. */
  @inline private def storeName(theStore: Store): String = 
    if(theStore == mcNotDoneStore) "mcNotDoneStore"
    else{ assert(theStore == mcDoneStore); "mcDoneStore" }

  /** Add missingInfo to theStore(cv), if not already there. */
  @inline private def addToStore(
    theStore: Store, cv: ReducedComponentView, missingInfo: MissingInfo)
      : Unit = {
    var done = false
    while(!done){
      val mis = theStore.getOrElseUpdate(cv, mkMissingInfoSet)
      mis.synchronized{
        if(mapsto(theStore, cv, mis)){
          if(!mis.add(missingInfo)) missingInfo.setNotAdded
          done = true
        }
      }
    }
  }

  /** Add missingInfo to theStore(cv), if not in the MissingInfoStore. */
  @inline private def maybeAddToStore(
    theStore: Store, cv: ReducedComponentView, missingInfo: MissingInfo)
  = 
    if(MissingInfoStore.add(missingInfo)) addToStore(theStore, cv, missingInfo)
    else Profiler.count("maybeAddToStore: MissingInfo not added") 

  /** Add MissingInfo(nv, missing, missingCommon) to the stores. 
    * This corresponds to transition trans inducing
    * cv == (pre.servers, oldCpts) -> (post.servers, newCpts) == newView. */
  def add(missing: List[ReducedComponentView], 
    missingCommon: List[MissingCommon], nv: ComponentView, trans: Transition, 
    oldCpts: Array[State], cv: ComponentView, newCpts: Array[State])
      : Unit = /*synchronized*/{
    Profiler.count("EffectOnStore.add")
    // I think the following holds regardless of concurrent threads: each mc
    // is created based on earlier plies; and any update will be based just on
    // the previous ply.
    for(mc <- missingCommon) assert(!mc.done)
    val mcArray = missingCommon.toArray
    val nv1 = new ReducedComponentView(nv.servers, nv.components)
    // Profiler.count(s"new MissingInfo ${mcArray.size} ${missing.length}")
    val missingInfo = new MissingInfo(nv1, missing.toArray, mcArray, 
      trans, oldCpts, cv, newCpts)
    if(missingCommon.isEmpty && !MissingInfoStore.add(missingInfo)) 
      // Doing this test when missingCommon.nonEmpty does very little 
      Profiler.count("add: MissingInfo not added ")
    else if(missingCommon.isEmpty){
      assert(missing.nonEmpty); missingInfo.transferred = true
      addToStore(mcDoneStore, missingInfo.missingHead, missingInfo)
    }
    else{
      val mc0 = mcArray(0); val princ1 = mc0.cpts1(0); val servers1 = mc0.servers
      // Add entries to mcMissingCandidates against the first MissingCommon.
      for(cpts <- mc0.missingHeads){ 
        assert(cpts != null)
        val cv = new ReducedComponentView(servers1, cpts)
        missingInfo.log(MissingInfo.McNotDoneStore(cv, ply))
        addToStore(mcNotDoneStore, cv, missingInfo)
      }
      // Add entries to candidateForMCStore.  All entries in missingCommon
      // correspond to the same key in candidateForMCStore...
      if(missingCommon.length > 1) for(mc <- missingCommon.tail)
        assert(mc.servers == servers1 && mc.cpts1(0) == princ1)
      // ... so it's enough to store against the key for mc0
      val key = (servers1, princ1); var done = false
      missingInfo.log(CandidateForMC(servers1, princ1, ply))
      while(!done){
        val mis = candidateForMCStore.getOrElseUpdate(key, mkMissingInfoSet)
        mis.synchronized{
          if(mapsto(candidateForMCStore, key, mis)){
            if(!mis.add(missingInfo)) missingInfo.setNotAdded
            done = true
          }
          // else another thread updated key, so go round the loop again
        }
      }
      // if(! mis.synchronized{ mis.add(missingInfo) }) missingInfo.setNotAdded
    }
  }

  import MissingCommon.CptsBuffer

  /* Helper functions for complete. */

  /** Add mi.newView to buff if not already there. */
  @inline private  def maybeAdd(mi: MissingInfo, buff: ViewBuffer) = {
    val nv = mi.newView
    if(!buff.contains(nv)){
      val newView = ComponentView.fromReducedComponentView(nv)
      newView.setCreationInfoIndirect(
        mi.pre, mi.oldCpts, mi.cv, mi.e, mi.post, mi.newCpts)
      buff += newView
    }
    else Profiler.count("maybeAdd repeat")
  }

  /** Update based upon the MissingCommon entries in mi being all completed.
    * Pre: the missingViews in mi have been updated (via mi.advanceMC).  If
    * now done, then add the newView to buff; otherwise add to mcDoneStore. */
  @inline private 
  def mcDone(mi: MissingInfo, views: ViewSet, buff: ViewBuffer) = {
    require(mi.mcDone); require(mi.missingViewsUpdated(views))
    if(mi.done) maybeAdd(mi, buff)
    else{
      mi.transferred = true
      // addToStore(mcDoneStore, mi.missingHead, mi)
      maybeAddToStore(mcDoneStore, mi.missingHead, mi)
      // IMPROVE: remove elsewhere
    }
  }

  /* The various phases of complete.  In each phase, we also purge all
   * MissingInfos for which the newView has been found, or are done.  In the
   * first two cases, we also purge those whose MissingCommon are done. */

  /** For each relevant entry in candidateForMCStore, try to match the
    *  MissingCommon entries against cv. */
  @inline private def completeCandidateForMC(
      cv: ComponentView, views: ViewSet, result: ViewBuffer): Unit = {
    val key = (cv.servers, cv.principal)
    candidateForMCStore.get(key) match{
      case Some(mis) => 
        val newMis = mkMissingInfoSet // those to retain
        var ok = true
        mis.synchronized{
          if(!mapsto(candidateForMCStore, key, mis))
            // The earlier read raced with another thread, which got the lock
            // on mis first; retry.
            ok = false 
          else{
            for(mi <- mis.iterator) mi.synchronized{
              // mi.log(MissingInfo.CCFMCIter(cv))
              if(mi.mcDone) assert(mi.done || mi.transferred)
              else if(views.contains(mi.newView)) mi.markNewViewFound
              else{
                if(MISFlag) MissingInfoStore.remove(mi)
                val vb: CptsBuffer = mi.updateMissingCommon(cv, views) //, key
                if(vb == null){
                  if(mi.done) maybeAdd(mi, result)
                  else{ assert(mi.mcDone); mcDone(mi, views, result) }
                }
                else if(!MISFlag || MissingInfoStore.add(mi)){
                  // Register mi against each view in vb, and retain
                  for(cpts <- vb){
                    val rcv = new ReducedComponentView(cv.servers, cpts)
                    // mi.log(MissingInfo.McNotDoneStore(rcv, ply))
                    addToStore(mcNotDoneStore, rcv, mi)
                  }
                  if(!newMis.add(mi)) mi.setNotAdded
                }
              }
            } // end of mi.synchronized / for loop
            // Update candidateForMCStore
            val ok1 =
              if(newMis.nonEmpty) 
                candidateForMCStore.compareAndSet(key,mis,newMis)
              else candidateForMCStore.removeIfEquals(key, mis)
            assert(ok1) // The locking protocol should ensure this
            // Note: the above needs to be inside the mis.synchronized block,
            // in case of a race with another thread where the order of
            // updating the store is the opposite of the order for obtaining
            // the lock: in this case, if the first thread successfully does a
            // MissingInfoStore.add(mi), the latter will fail, and mi will be
            // lost.
          } // end of else clause
        } // end of mis.synchronized
        if(!ok){
          Profiler.count("completeCandidateForMC retry")
          completeCandidateForMC(cv, views, result)
        }

      case None => {}
    }
  }

  /** Remove cv from the missingViews of the MissingCommon of each entry in
    * mcNotDoneStore. */
  @inline private def completeMcNotDone(
      cv: ComponentView, views: ViewSet, result: ViewBuffer) = {
    mcNotDoneStore.remove(cv) match{
      case Some(mis) =>
        mis.synchronized{
          for(mi <- mis.iterator) mi.synchronized{
            // mi.log(MissingInfo.CMNDIter(cv, ply))
            if(mi.mcDone) assert(mi.done || mi.transferred)
            else if(views.contains(mi.newView)) mi.markNewViewFound
            else{
              if(MISFlag) MissingInfoStore.remove(mi)
              val vb = mi.updateMissingViewsOfMissingCommon(views)
              if(vb == null){
                if(mi.done) maybeAdd(mi, result)
                else{ assert(mi.mcDone); mcDone(mi, views, result) }
              }
              else if(!MISFlag || MissingInfoStore.add(mi)){
                for(cpts <- vb){
                  val rcv = new ReducedComponentView(cv.servers, cpts)
                  // mi.log(McNotDoneStore(rcv, ply))
                  addToStore(mcNotDoneStore, rcv, mi)
                }
              }
              else Profiler.count("MissingInfo not added")
            }
          } // end of mi.synchronized and for loop
        } // end of mis.synchronized

      case None => {}
    }
  }

  /** Remove cv from each entry in mcDoneStore. */
  @inline private 
  def completeMcDone(cv: ComponentView, views: ViewSet, result: ViewBuffer) = {
    mcDoneStore.remove(cv) match{
      case Some(mis) =>
        mis.synchronized{
          for(mi <- mis.iterator) mi.synchronized{
            if(!mi.done){
              if(views.contains(mi.newView)) mi.markNewViewFound
              else{ 
                // Would it be better to do the remove later?
                MissingInfoStore.remove(mi)
                mi.updateMissingViewsBy(cv, views)
                if(mi.done) maybeAdd(mi, result)
                else maybeAddToStore(mcDoneStore, mi.missingHead, mi)
              }
            }
          } // end of mi.synchronized, for loop
        } // end of mis.synchronized

      case None => {}
    }
  }

  /** Try to complete values in the store, based on the addition of cv, and with
    * views as the current ViewSet (i.e. from earlier plies).  Return the
    * Views that can now be added.  */
  def complete(cv: ComponentView, views: ViewSet): ViewBuffer = {
    // In each phase below, we also purge all MissingInfos for which the
    // newView has been found, or are done.  In the first two cases, we also
    // purge those whose MissingCommon are done.
    var result = new ViewBuffer
    // For each relevant entry in candidateForMCStore, try to match the
    // MissingCommon entries against cv.
    completeCandidateForMC(cv, views, result)
    // Remove cv from the missingViews of the MissingCommon of each entry in
    // mcNotDoneStore.
    completeMcNotDone(cv, views, result)
    // Remove cv from each entry in mcDoneStore.  
    completeMcDone(cv, views, result)
    result
  }

  // ====================== Purging

  import ShardedHashMap.ShardIteratorProducerT

  /** Object to produce iterators over the shards of candidateForMCStore. */
  private var candidateForMCStoreShardIterator: 
      ShardIteratorProducerT[(ServerStates, State), MissingInfoSet] = null

  type StoreShardIterator = 
    ShardIteratorProducerT[ReducedComponentView, MissingInfoSet]

  /** Object to produce iterators over the shards of mcNotDoneShardIterator. */
  private var mcNotDoneShardIterator: StoreShardIterator = null

  /** Object to produce iterators over the shards of mcDoneShardIterator. */
  private var mcDoneShardIterator: StoreShardIterator = null

  /** Prepare for the next calls to purge. */
  def prepareForPurge = {
    candidateForMCStoreShardIterator = candidateForMCStore.shardIteratorProducer
    mcNotDoneShardIterator = mcNotDoneStore.shardIteratorProducer
    mcDoneShardIterator = mcDoneStore.shardIteratorProducer
  }

  /** Attempt to purge entries from the stores that are no longer needed. */
  def purgeCandidateForMCStore(views: ViewSet) = {
    // Purge from candidateForMCStore
    var shardIterator = candidateForMCStoreShardIterator.get
    while(shardIterator != null){
      while(shardIterator.hasNext){
        val (key,mis) = shardIterator.next(); val misIter = mis.iterator
        val newMis = mkMissingInfoSet; var changed = false
        while(misIter.hasNext){
          val mi = misIter.next()
          if(!mi.done && !mi.getMcDone && !mi.isNewViewFound(views) &&
              (!MISFlag || !MissingInfoStore.removeIfProperSubset(mi)) )
            newMis += mi
          else{ Profiler.count("candidateForMCStore.purge"); changed = true }
        } // end of iteration over misIter
        if(changed){
          if(newMis.nonEmpty) candidateForMCStore.replace(key, newMis)
          else candidateForMCStore.remove(key)
        }
      } // end of iteration over shardIterator
      shardIterator = candidateForMCStoreShardIterator.get
    } // end of outer iteration
  }

  /** Purge from mcNotDoneStore. */
  def purgeMCNotDone(views: ViewSet) = {
    var shardIterator = mcNotDoneShardIterator.get
    while(shardIterator != null){
      while(shardIterator.hasNext){
        val (v, mis) = shardIterator.next(); val misIter = mis.iterator
        val newMis = mkMissingInfoSet; var changed = false
        // for(mi <- mis){
        while(misIter.hasNext){
          val mi = misIter.next()
          // IMPROVE: could replace getMcDone by mcDone, and in purge
          if(!mi.done && !mi.getMcDone && !mi.isNewViewFound(views) &&
               (!MISFlag || !MissingInfoStore.removeIfProperSubset(mi)) ) 
            newMis += mi
          else{ Profiler.count("mcNotDone.purge"); changed = true }
        }
        if(changed){
          if(newMis.nonEmpty) mcNotDoneStore.replace(v,newMis)
          else mcNotDoneStore.remove(v)
        }
      } // end of iteration over shardIterator
      shardIterator = mcNotDoneShardIterator.get
    }
  }

  /** Purge from store. */
  def purgeMCDone(views: ViewSet) = {
    var shardIterator = mcDoneShardIterator.get
    while(shardIterator != null){
      while(shardIterator.hasNext){
        val (v, mis) = shardIterator.next()
        val newMis = mkMissingInfoSet; var changed = false
        for(mi <- mis.iterator){
          if(!mi.done && !mi.isNewViewFound(views) &&
               !MissingInfoStore.removeIfProperSubset(mi))
            newMis += mi
          else{ Profiler.count("mcDone.purge"); changed = true }
        }
        if(changed){
          if(newMis.nonEmpty) mcDoneStore.replace(v,newMis)
          else mcDoneStore.remove(v)
        }
      } // end of iteration over shardIterator
      shardIterator = mcDoneShardIterator.get
    }
  }

  // ====================== sanity check and reporting

  /** Perform sanity check.  Every stored MissingInfo should be up to date,
    * unless it has maybe been superseded by an equivalent object.  */
  def sanityCheck(views: ViewSet) = {
    println("Sanity check")
    // Do sanity check on all entries of iter.  If flag then they are expected
    // to satisfy mcDone.
    def doCheck(iter: Iterator[MissingInfoSet], flag: Boolean) = 
      for(mis <- iter; mi <- mis.iterator; if !mi.done) 
        mi.sanityCheck(views, flag)

    doCheck(mcDoneStore.valuesIterator, true)
    // Catch in following for debugging
    for((cv,mis) <- mcNotDoneStore.iterator; mi <- mis.iterator; if !mi.done){
      try{  mi.sanityCheck(views, false) }
      catch{ 
        case e: java.lang.AssertionError => {
          e.printStackTrace
          println(s"\ncv = $cv. "+views.contains(mi.newView)+s"\nmi = $mi")
          sys.exit()
        }
      }
    }
    doCheck(candidateForMCStore.valuesIterator, false)
  }

  /** Report on size. */
  def report = {
    // The number of MissingInfos in iter; the number of views in their
    // missingViews; and the number of views in their missingCommons
    def count(iter: Iterator[MissingInfoSet]): (Long, Long, Long) = {
      // # items in iter, and sum of their sizes
      var numEls = 0L; var mvSize = 0L; var mcSize  = 0L
      for(mis <- iter; mi <- mis.iterator){ 
        numEls += 1; val (mvSize1,mcSize1) = mi.size
        mvSize += mvSize1; mcSize += mcSize1
      }
      (numEls, mvSize, mcSize)
    }
    println()

    println("allMCs: size = "+printLong(MissingCommon.allMCsSize))
    println("candidateForMCStore: size = "+candidateForMCStore.size)
    val (cStoreEls, cStoreMVSize, cStoreMCSize) = 
      count(candidateForMCStore.valuesIterator)
    println("  # MissingInfos = "+printLong(cStoreEls))
    println("  MissingInfos missingViews size = "+printLong(cStoreMVSize))
    println("  MissingInfos missingCommon size = "+printLong(cStoreMCSize))

    println("mcNotDoneStore: size = "+mcNotDoneStore.size)
    val (mcmStoreEls, mcmStoreMVSize, mcmStoreMCSize) = 
      count(mcNotDoneStore.valuesIterator)
    println("  # MissingInfos = "+printLong(mcmStoreEls))
    println("  MissingInfos missingViews size = "+printLong(mcmStoreMVSize))
    println("  MissingInfos missingCommons size = "+printLong(mcmStoreMCSize))

    println("mcDoneStore: size = "+mcDoneStore.size)
    val (storeEls, storeMVSize, storeMCSize) = count(mcDoneStore.valuesIterator)
    println("  # MissingInfos = "+printLong(storeEls))
    println("  MissingInfos missingViews size = "+printLong(storeMVSize))
    println("  MissingInfos missingCommon size = "+printLong(storeMCSize))

  }

  /** Perform a memory profile of this. */
  def memoryProfile = {
    import ox.gavin.profiling.MemoryProfiler.traverse
    // profile MissingCommon, MissingInfoStore
    MissingCommon.memoryProfile
    println("MissingInfoStore.size = "+printLong(MissingInfoStore.size))
    traverse("MissingInfoStore", MissingInfoStore, maxPrint = 3)
    println()

    println("mcNotDoneStore: size = "+mcNotDoneStore.size)
    var iter = mcNotDoneStore.valuesIterator; var count = 0; val Max = 3
    while(iter.hasNext && count < Max){
      val mis: MissingInfoSet = iter.next(); val miIter = mis.iterator
      while(miIter.hasNext && count < Max){
        val mi: MissingInfo = miIter.next();
        traverse("missingInfo", mi, maxPrint = 0); count += 1; println()
      }
    }

    traverse("mcNotDoneStore", mcNotDoneStore, maxPrint = 2); println()
    traverse("mcDoneStore", mcDoneStore, maxPrint = 2); println()
    traverse("candidateForMCStore", candidateForMCStore, maxPrint = 2); println()
    traverse("effectOnStore", this, maxPrint = 1); println()
  }

}

/* Each MissingInfo is stored in the SimpleEffectOnStore as follows.
 * 
 * If the requirements for condition (c) of the relevant definition are not
 * satisfied, then it is stored:
 * 
 * - In candidateForMCStore, keyed against (servers,cpts(0)) for each
 *   MissingCommon(servers,cpts,_,_) representing a conjunct of condition (c).
 * 
 * - In mcNotDoneStore, keyed against each elements of mc.missingHeads, where
 *   mc is the MissingCommon representing the next conjunct of condition (c).
 * 
 * If the requirements for condition (c) are satisfied, it is stored in
 * mcDoneStore, keyed against its missingHead, i.e. the next required View.
 * 
 * In addition, candidateForMCStore and mcNotDoneStore might hold MissingInfo
 * objects for which condition (c) has been satisfied.  A copy will have been
 * added to mcDoneStore (if the object is not done), indicated by its
 * transferred field.  These objects can be purged from those stores.
 */
