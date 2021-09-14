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

  /** Add MissingInfo(nv, missing, missingCommon) to the store. */
  def add(missing: List[ComponentView], missingCommon: List[MissingCommon], 
    nv: ComponentView): Unit

  /** Try to complete values in the store, based on the addition of cv, and with
    * views as the ViewSet.  Return the Views that can now be added.  */
  def complete(cv: ComponentView, views: ViewSet): List[ComponentView]

  /** Sanity check performed at the end of a run. */
  def sanityCheck(views: ViewSet): Unit

  def size: (Int, Int)

  def report: Unit
}

// =======================================================

/** A simple implementation of EffectOnStore. */
class SimpleEffectOnStore extends EffectOnStore{
  /* Overview of main functions.
   * 
   * add
   * |--addToStore
   * 
   * complete
   * |--mcDone
   *    |--(MissingInfo).{mcDone,updateMissingViews,done}
   */

  /** A set of MissingInfos.
    * IMPROVE: remove redundancies? */
// FIXME: hashes not correct
  type MissingInfoSet = HashSet[MissingInfo]

  /** A type of stores, giving the MissingInfos that might need updating as the
    * result of finding a new ComponentView. */
  type Store = HashMap[ComponentView, MissingInfoSet]

  /** Information about those mi: MissingInfo in the abstract set such that
    * !mi.mcDone (i.e. not all MissingCommon in mi.missingCommon are done).
    * If mc is the first element of mi.missingCommon that is not done, then
    * for each v in mc.missingHeads, mcMissingCandidatesStore contains v -> mi
    * (i.e. keyed against the next missing view in each option within mc). */
  private val mcMissingCandidatesStore = new Store

  /** Information about those mi: MissingInfo in the abstract set such that
    * mi.mcDone (i.e. all MissingCommon in mi.missingCommon are done).  For
    * each such mi, store contains mi.missingHead -> mi (i.e. keyed against
    * the next missing view). */
  private val store = new Store

  /** The underlying store concerning MissingCommon values.  For each mi:
    * MissingInfo in the abstract set, and for each
    * MissingCommon(servers,cpts,_,_) or (servers,_,cpts,_) in
    * mi.missingCommon, commonStore(servers,cpts(0)) contains mi.  This is
    * used to identify whether a new view can be used to instantiate c in the
    * obligation of the missingCommon.  */
// FIXME: seems to be just the former.  Maybe that's enough.
// IMPROVE: include the pid in the domain of the mapping.
// IMPROVE: store only against the first MissingCommon.
  private val commonStore = new HashMap[(ServerStates, State), MissingInfoSet]

  /** Add missingInfo to theStore(cv), if not already there. */
  private 
  def addToStore(theStore: Store, cv: ComponentView, missingInfo: MissingInfo)
  = {
    theStore.get(cv) match{
      case Some(mis) => mis += missingInfo 
      case None =>
        val mis = new MissingInfoSet; mis += missingInfo
        theStore += cv -> mis
    }
  }

  /** Add MissingInfo(nv, missing, missingCommon) to the stores. */
  def add(missing: List[ComponentView], missingCommon: List[MissingCommon], 
    nv: ComponentView)
      : Unit = {
    Profiler.count("EffectOnStore.add")
    val missingInfo = new MissingInfo(nv, missing.toArray, missingCommon.toArray)
    if(missingCommon.isEmpty){
      assert(missing.nonEmpty)
      addToStore(store, missingInfo.missingHead, missingInfo)
    }
    else{
      // Add entries to mcMissingCandidates
      for(cv <- missingCommon(0).missingHeads)
        addToStore(mcMissingCandidatesStore, cv, missingInfo)
      // Add entries to commonStore.  IMPROVE: register just against
      // mi.missingHead
      for(mc <- missingCommon){
// FIXME: also cpts2? 
        val princ1 = mc.cpts1(0)
        if(false && debugging)
          assert(Remapper.remapToPrincipal(mc.servers, princ1) == princ1)
        val key = (mc.servers, princ1)
        commonStore.get(key) match{
          case Some(mis) => mis += missingInfo
          case None => 
            val mis = new MissingInfoSet; mis += missingInfo
            commonStore += key -> mis
        }
        // val prev = 
        //   commonStore.getOrElse((mc.servers, princ1), List[MissingInfo]())
        // //if(!contains(prev,missingInfo)) // needs equality test
        // commonStore += (mc.servers, princ1) -> (missingInfo::prev)
        // //else println("Already stored "+missingInfo)
      }
    }
  }

  private def contains(cvs: List[MissingInfo], cv: MissingInfo): Boolean = 
    cvs.nonEmpty && (cvs.head == cv || cvs.tail.contains(cv))

  import MissingCommon.ViewBuffer

  /** Try to complete values in the store, based on the addition of cv, and with
    * views as the ViewSet.  Return the Views that can now be added.  */
  def complete(cv: ComponentView, views: ViewSet): List[ComponentView] = {
    var result = List[ComponentView]()
    // Add nv to result if not already there
    def maybeAdd(nv: ComponentView) = if(!result.contains(nv)) result ::= nv

    // Update based upon the MissingCommon entries in mi being all completed.
    // Update its missingViews; if now done, then add the newView to result;
    // otherwise add to store.
    def mcDone(mi: MissingInfo) = {
      require(mi.mcDone)
      mi.updateMissingViews(views)
      if(mi.done) maybeAdd(mi.newView)
      else addToStore(store, mi.missingHead, mi)
      // mi.sanity1
    }

    // In each phase below, we also purge all MissingInfos for which the
    // newView has been found, or are done.  In the first two cases, we also
    // purge those whose MissingCommon are done.

    // For each relevant entry in commonStore, try to match the MissingCommon
    // entries against cv. 
    val key = (cv.servers, cv.principal)
    commonStore.get(key) match{
      case Some(mis) => 
        val newMis = new MissingInfoSet  // those to retain in commonStore(key)
        for(mi <- mis; if !mi.mcDone){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else{
            val vb : ViewBuffer =  mi.updateMissingCommon(cv, views)
            if(mi.done) maybeAdd(mi.newView)
            else if(mi.mcDone) mcDone(mi)
            else{
              // Register mi against each view in vb, and retain in commonStore
              for(cv1 <- vb) addToStore(mcMissingCandidatesStore, cv1, mi)
              newMis += mi
            }
          }
          // mi.sanity1
        } // end of for loop
        //if(newMis.length != mis.length){
        if(newMis.nonEmpty) commonStore += key -> newMis
        else commonStore.remove(key)
        //}
      case None => {}
    }

    // Remove cv from the missingViews of the MissingCommon of each entry in
    // mcMissingCandidateStore.
    mcMissingCandidatesStore.get(cv) match{
      case Some(mis) =>
        mcMissingCandidatesStore.remove(cv) // remove old entry
        for(mi <- mis; if !mi.mcDone){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else{
            val ab = mi.updateMissingViewsOfMissingCommon(cv, views) 
            if(mi.done) maybeAdd(mi.newView) 
            else if(mi.mcDone) mcDone(mi) 
            else for(cv1 <- ab) addToStore(mcMissingCandidatesStore, cv1, mi)
          }
          // mi.sanity1
        } // end of for loop
      case None => {}
    }

    // Remove cv from each entry in store.  
    store.get(cv) match{
      case Some(mis) =>
        store.remove(cv) // remove old entry
        for(mi <- mis; if !mi.done){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else{
            mi.updateMissingViewsBy(cv, views)
            if(mi.done) maybeAdd(mi.newView)
            else addToStore(store, mi.missingHead, mi)
          }
          // mi.sanity1
        } // end of for loop
      case None => {}
    }

    result
  }

  def size = (store.size, commonStore.size)

  /** Check that every stored MissingInfo is either done or contains no element
    * of views. */
  def sanityCheck(views: ViewSet) = {
    println("Sanity check")
    // Do sanity check on all entries of iter.  If flag then they are expected
    // to satisfy mcDone.
    def doCheck(iter: Iterator[Iterable[MissingInfo]], flag: Boolean) = 
      for(mis <- iter; mi <- mis; if !mi.done) mi.sanityCheck(views, flag)
    doCheck(store.valuesIterator, true)
    doCheck(mcMissingCandidatesStore.valuesIterator, false)
    doCheck(commonStore.valuesIterator, false)
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
          // Profiler.count("MissingCommon length "+mi.mcCount)
      (numEls, mvSize, mcSize)
    }
    println
    println("store: size = "+store.size)
    val (storeEls, storeMVSize, storeMCSize) = count(store.valuesIterator)
    println("  # MissingInfos = "+printLong(storeEls))
    println("  MissingInfos missingViews size = "+printLong(storeMVSize))
    println("  MissingInfos missingCommon size = "+printLong(storeMCSize))

    println("commonStore: size = "+commonStore.size)
    val (cStoreEls, cStoreMVSize, cStoreMCSize) = 
      count(commonStore.valuesIterator)
    println("  # MissingInfos = "+printLong(cStoreEls))
    println("  MissingInfos missingViews size = "+printLong(cStoreMVSize))
    println("  MissingInfos missingCommon size = "+printLong(cStoreMCSize))

    println("mcMissingCandidatesStore: size = "+mcMissingCandidatesStore.size)
    val (mcmStoreEls, mcmStoreMVSize, mcmStoreMCSize) = 
      count(mcMissingCandidatesStore.valuesIterator)
    println("  # MissingInfos = "+printLong(mcmStoreEls))
    println("  MissingInfos missingViews size = "+printLong(mcmStoreMVSize))
    println("  MissingInfos missingCommons size = "+printLong(mcmStoreMCSize))
    println

    // Find key with largest image
    // val maxKey = store.keys.maxBy(k => store(k).length)
    // println(s"maxKey = $maxKey -> ")
    // for(mi <- store(maxKey)) println(mi)
  }

}
