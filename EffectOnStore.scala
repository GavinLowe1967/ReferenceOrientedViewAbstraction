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
    * This corresponds to transition pre -e-> post inducing
    * cv == (pre.servers, oldCpts) -> (post.servers, newCpts) == newView.*/
  def add(missing: List[ReducedComponentView], 
    missingCommon: List[MissingCommon],
    nv: ComponentView,
    pre: Concretization, oldCpts: Array[State], cv: ComponentView,
    e: EventInt, post: Concretization, newCpts: Array[State]): Unit

  /** Try to complete values in the store, based on the addition of cv, and with
    * views as the ViewSet.  Return the Views that can now be added.  */
  def complete(cv: ComponentView, views: ViewSet): ArrayBuffer[ComponentView]

  /** Sanity check performed at the end of a run. */
  def sanityCheck(views: ViewSet): Unit

  // def size: (Int, Int)

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
   * |--mcDone
   *    |--(MissingInfo).{mcDone,updateMissngViews,done}
   */

  /** A set of MissingInfos. */
  type MissingInfoSet = HashSet[MissingInfo]

  /** A type of stores, giving the MissingInfos that might need updating as the
    * result of finding a new ComponentView. */
  //type Store = HashMap[ReducedComponentView, MissingInfoSet]
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
// IMPROVE: include the pid in the domain of the mapping.
// IMPROVE: store only against the first MissingCommon.  This would require
// MissingInfo.advanceMC calling updateWithNewMatch on the new MissingCommon.
  private val candidateForMCStore = 
    new HashMap[(ServerStates, State), MissingInfoSet]

  /* Operations on each of the above HashMaps is protected by a synchronized
   * block on that HashMap.  Operations on each MissingInfoSet is protected by
   * a synchronized block on that MissingInfoSet. */

/* IMPROVE: periodically purge the stores of MissingInfos that are done or for
 * which the newView has been found, and purge mcNotDoneStore and
 * candidateForMSCStore of MissingInfos that are mcDone. */

  import MissingInfo.{LogEntry, McDoneStore, McNotDoneStore,
    CandidateForMC, NotStored}

  /** Name of theStore.  Used in logging for debugging. */
  @inline private def storeName(theStore: Store): String = 
    if(theStore == mcNotDoneStore) "mcNotDoneStore"
    else{ assert(theStore == mcDoneStore); "mcDoneStore" }

  /** Add missingInfo to theStore(cv), if not already there. */
  @inline private def addToStore(
    theStore: Store, cv: ReducedComponentView, missingInfo: MissingInfo)
  = {
    val mis =
      /*theStore.synchronized*/{ theStore.getOrElseUpdate(cv, new MissingInfoSet) }
    if(! mis.synchronized{ mis.add(missingInfo) }){
      missingInfo.setNotAdded; //missingInfo.log(NotStored(storeName(theStore)))
    } 
  }
  // /** Add missingInfo to theStore(cv), if not already there. */
  // @inline private def addToStore(
  //   theStore: Store1, cv: ReducedComponentView, missingInfo: MissingInfo)
  // = {
  //   val mis = theStore.getOrElseUpdate(cv, new MissingInfoSet) 
  //   if(! mis.synchronized{ mis.add(missingInfo) }){
  //     missingInfo.setNotAdded; //missingInfo.log(NotStored(storeName(theStore)))
  //   } 
  // }

  /** Add MissingInfo(nv, missing, missingCommon) to the stores. 
    * This corresponds to transition pre -e-> post inducing
    * cv == (pre.servers, oldCpts) -> (post.servers, newCpts) == newView. */
  def add(missing: List[ReducedComponentView], 
    missingCommon: List[MissingCommon], nv: ComponentView,
    pre: Concretization, oldCpts: Array[State], cv: ComponentView,
    e: EventInt, post: Concretization, newCpts: Array[State])
      : Unit = {
    // if(ComponentView0.highlight(nv))
    //   println(s"\nEffectOnStore.add($nv);\n missingCommon = $missingCommon;\n"+
    //     s"missing = "+missing.mkString("List(", ",\n    ", ")")+
    //     s"\nFrom\n$pre ->\n  $post induces\n"+
    //     EffectOnStore.showInduced(cv, oldCpts, post.servers, newCpts, nv))
    Profiler.count("EffectOnStore.add")
    // I think the following holds regardless of concurrent threads: each mc
    // is created based on earlier plies; and any update will be based just on
    // the previous ply.
    for(mc <- missingCommon) assert(!mc.done)
    val mcArray = missingCommon.toArray
    val nv1 = new ReducedComponentView(nv.servers, nv.components)
    val missingInfo = new MissingInfo(nv1, missing.toArray, mcArray, 
      pre, oldCpts, cv, e, post, newCpts)
    if(missingCommon.isEmpty){
      assert(missing.nonEmpty)
      // missingInfo.log(McDoneStore(missingInfo.missingHead))
      missingInfo.transferred = true
      addToStore(mcDoneStore, missingInfo.missingHead, missingInfo)
    }
    else{
      val mc0 = mcArray(0)
      // Add entries to mcMissingCandidates against the first MissingCommon.
      // Note: mcArray may be in a different order from missingCommon.
      for(cpts <- mc0.missingHeads){ 
        val cv = new ReducedComponentView(mc0.servers, cpts)
        // missingInfo.log(McNotDoneStore(cv))
        addToStore(mcNotDoneStore, cv, missingInfo)
      }
      // Add entries to candidateForMCStore.  IMPROVE: register just against
      // mcArray(0)
      for(mc <- missingCommon){
        val princ1 = mc.cpts1(0); val key = (mc.servers, princ1)
        val mis = candidateForMCStore.synchronized{ 
          candidateForMCStore.getOrElseUpdate(key, new MissingInfoSet) 
        }
        // missingInfo.log(CandidateForMC(mc.servers,princ1))
        if(! mis.synchronized{ mis.add(missingInfo) }){
          missingInfo.setNotAdded; 
          // missingInfo.log(NotStored("candidateForMCStore -- add"))
        }
      }
    }
  }

  import MissingCommon.CptsBuffer

  /* Helper functions for complete. */

  /** Add mi.newView to result if not already there. */
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
      // mi.log(McDoneStore(mi.missingHead))
      mi.transferred = true
      addToStore(mcDoneStore, mi.missingHead, mi)
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
    candidateForMCStore.synchronized{ candidateForMCStore.get(key) } match{
      case Some(mis) => 
        val newMis = new MissingInfoSet // those to retain
        mis.synchronized{
          for(mi <- mis) mi.synchronized{
            if(mi.mcDone) assert(mi.done || mi.transferred)
            else if(views.contains(mi.newView)) mi.markNewViewFound
            else{
              val vb: CptsBuffer = mi.updateMissingCommon(cv, views)
              if(vb == null){
                if(mi.done) maybeAdd(mi, result)
                else{ assert(mi.mcDone); mcDone(mi, views, result) }
              }
              else{
                // Register mi against each view in vb, and retain
                for(cpts <- vb){
                  val rcv = new ReducedComponentView(cv.servers, cpts)
                  // assert(!views.contains(cv1))
                  // mi.log(McNotDoneStore(rcv))
                  addToStore(mcNotDoneStore, rcv, mi)
                }
                // mi.log(CandidateForMC(cv.servers, cv.principal))
                if(!newMis.add(mi)){
                  mi.setNotAdded; mi.log(NotStored("candidateForMCStore"))
                }
              }
            }
          } // end of mi.synchronized / for loop
        } // end of mis.synchronized

        // Update candidateForMCStore if this mapping hasn't changed.
        var ok = true
        if(newMis.nonEmpty) candidateForMCStore.synchronized{
          if(candidateForMCStore.get(key) == Some(mis))
            candidateForMCStore += key -> newMis
          else ok = false
        }
        else candidateForMCStore.synchronized{ 
          if(candidateForMCStore.get(key) == Some(mis))
            candidateForMCStore.remove(key)
          else ok = false
        }
        /*
        candidateForMCStore.synchronized{
          if(candidateForMCStore.get(key) == Some(mis)){
            if(newMis.nonEmpty) candidateForMCStore += key -> newMis
            else candidateForMCStore.remove(key)
          }
          else ok = false // the relevant mapping changed, so retry
        }
         */
        if(!ok){
          Profiler.count("completeCandidateForMC retry") // a few times per MState
          completeCandidateForMC(cv, views, result)
        }

      case None => {}
    }
  }

  /** Remove cv from the missingViews of the MissingCommon of each entry in
    * mcNotDoneStore. */
  @inline private def completeMcNotDone(
      cv: ComponentView, views: ViewSet, result: ViewBuffer) = {
    /*mcNotDoneStore.synchronized*/{ mcNotDoneStore.remove(cv) } match{
      case Some(mis) =>
        // remove old entry
        // mcNotDoneStore.synchronized{ mcNotDoneStore.remove(cv) } 
        mis.synchronized{
          for(mi <- mis) mi.synchronized{
            if(mi.mcDone) assert(mi.done || mi.transferred)
            else if(views.contains(mi.newView)) mi.markNewViewFound
            else{
              val vb = mi.updateMissingViewsOfMissingCommon(views)
              if(vb == null){
                if(mi.done) maybeAdd(mi, result)
                else{ assert(mi.mcDone); mcDone(mi, views, result) }
              }
              else for(cpts <- vb){
                val rcv = new ReducedComponentView(cv.servers, cpts)
                // mi.log(McNotDoneStore(rcv))
                addToStore(mcNotDoneStore, rcv, mi)
              }
            }
          } // end of mi.synchronized and for loop
        } // end of mis.synchronized

      case None => {}
    }
  }

  /** Remove cv from each entry in mcDoneStore. */
  @inline private 
  def completeMcDone(cv: ComponentView, views: ViewSet, result: ViewBuffer) = {
    /*mcDoneStore.synchronized*/{ mcDoneStore.remove(cv) } match{
      case Some(mis) =>
        mis.synchronized{
          for(mi <- mis) mi.synchronized{
            if(!mi.done){
              if(views.contains(mi.newView)) mi.markNewViewFound
              else{
                mi.updateMissingViewsBy(cv, views)
                if(mi.done) maybeAdd(mi, result)
                else{
                  // mi.log(McDoneStore(mi.missingHead))
                  addToStore(mcDoneStore, mi.missingHead, mi)
                }
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
    var result = new ViewBuffer

    // In each phase below, we also purge all MissingInfos for which the
    // newView has been found, or are done.  In the first two cases, we also
    // purge those whose MissingCommon are done.

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

  /** Perform sanity check.  Every stored MissingInfo should be up to date,
    * unless it has maybe been superseded by an equivalent object.  */
  def sanityCheck(views: ViewSet) = {
    println("Sanity check")
    // Do sanity check on all entries of iter.  If flag then they are expected
    // to satisfy mcDone.
    def doCheck(iter: Iterator[Iterable[MissingInfo]], flag: Boolean) = 
      for(mis <- iter; mi <- mis; if !mi.done) mi.sanityCheck(views, flag)

    doCheck(mcDoneStore.valuesIterator, true)
    // Catch in following for debugging
    for((cv,mis) <- mcNotDoneStore.iterator; mi <- mis; if !mi.done){
      try{  mi.sanityCheck(views, false) }
      catch{ 
        case e: java.lang.AssertionError => {
          e.printStackTrace
          println(s"\ncv = $cv. "+ // views.contains(cv)+"; "+
            views.contains(mi.newView))
          println(s"\nmi = $mi")
          // println("log = "+mi.theLog.reverse.mkString("\n"))
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
    def count(iter: Iterator[Iterable[MissingInfo]]): (Long, Long, Long) = {
      // # items in iter, and sum of their sizes
      var numEls = 0L; var mvSize = 0L; var mcSize  = 0L
      for(mis <- iter; mi <- mis){ 
        numEls += 1; val (mvSize1,mcSize1) = mi.size
        mvSize += mvSize1; mcSize += mcSize1
      }
      (numEls, mvSize, mcSize)
    }
    println()

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
    // profile Max MissingCommons
    MissingCommon.memoryProfile
    println("mcNotDoneStore: size = "+mcNotDoneStore.size)
    var iter = mcNotDoneStore.valuesIterator; var count = 0; val Max = 3
    while(iter.hasNext && count < Max){
      val mis: MissingInfoSet = iter.next(); val miIter = mis.iterator
      //println(mis.size)
      while(miIter.hasNext && count < Max){
        val mi: MissingInfo = miIter.next();
        // for(mc <- mi.missingCommon; if mc != null){
        //   traverse("missingCommon", mc, maxPrint = 1); println; count += 1
        // }
        traverse("missingInfo", mi, maxPrint = 1); count += 1; println()
      }
    }

    traverse("mcNotDoneStore", mcNotDoneStore, maxPrint = 1); println()
    traverse("mcDoneStore", mcDoneStore, maxPrint = 1); println()
    traverse("candidateForMCStore", candidateForMCStore, maxPrint = 1); println()
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
