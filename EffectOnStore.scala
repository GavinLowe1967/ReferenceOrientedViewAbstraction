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

  // def size: (Int, Int)

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
  type MissingInfoSet = HashSet[MissingInfo]
  // IMPROVE: it's not clear that this ever detects equal values. 

  /** A type of stores, giving the MissingInfos that might need updating as the
    * result of finding a new ComponentView. */
  type Store = HashMap[ComponentView, MissingInfoSet]

  /** Information about those mi: MissingInfo in the abstract set such that
    * !mi.mcDone (i.e. not all MissingCommon in mi.missingCommon are done).
    * If mc is the first element of mi.missingCommon that is not done, then
    * for each v in mc.missingHeads, mcNotDoneStore contains
    * v -> mi (i.e. keyed against the next missing view in each option within
    * mc). */
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

  /** Add missingInfo to theStore(cv), if not already there. */
  @inline private 
  def addToStore(theStore: Store, cv: ComponentView, missingInfo: MissingInfo)
  = {
    val mis = theStore.getOrElseUpdate(cv, new MissingInfoSet)
    mis += missingInfo
    // theStore.get(cv) match{
    //   case Some(mis) => mis += missingInfo 
    //   case None =>
    //     val mis = new MissingInfoSet; mis += missingInfo
    //     theStore += cv -> mis
    // }
  }

  /** Add MissingInfo(nv, missing, missingCommon) to the stores. */
  def add(missing: List[ComponentView], missingCommon: List[MissingCommon], 
    nv: ComponentView)
      : Unit = {
    Profiler.count("EffectOnStore.add")
    val missingInfo = new MissingInfo(nv, missing.toArray, missingCommon.toArray)
    if(missingCommon.isEmpty){
      assert(missing.nonEmpty)
      addToStore(mcDoneStore, missingInfo.missingHead, missingInfo)
    }
    else{
      // Add entries to mcMissingCandidates
      for(cv <- missingCommon(0).missingHeads)
        addToStore(mcNotDoneStore, cv, missingInfo)
      // Add entries to candidateForMCStore.  IMPROVE: register just against
      // missingCommon(0)
      for(mc <- missingCommon){
        val princ1 = mc.cpts1(0); val key = (mc.servers, princ1)
        val mis = candidateForMCStore.getOrElseUpdate(key, new MissingInfoSet)
        mis += missingInfo
        // candidateForMCStore.get(key) match{
        //   case Some(mis) => mis += missingInfo
        //   case None => 
        //     val mis = new MissingInfoSet; mis += missingInfo
        //     candidateForMCStore += key -> mis
        // }
      }
    }
  }

  // private def containsX(cvs: List[MissingInfo], cv: MissingInfo): Boolean = 
  //   cvs.nonEmpty && (cvs.head == cv || cvs.tail.contains(cv))

  import MissingCommon.ViewBuffer

  /** Try to complete values in the store, based on the addition of cv, and with
    * views as the ViewSet.  Return the Views that can now be added.  */
  def complete(cv: ComponentView, views: ViewSet): List[ComponentView] = {
    var result = List[ComponentView]()
    // Add nv to result if not already there
    @inline def maybeAdd(nv: ComponentView) = 
      if(!result.contains(nv)) result ::= nv

    // Update based upon the MissingCommon entries in mi being all completed.
    // Update its missingViews; if now done, then add the newView to result;
    // otherwise add to mcDoneStore.
    @inline def mcDone(mi: MissingInfo) = {
      require(mi.mcDone); mi.updateMissingViews(views)
      if(mi.done) maybeAdd(mi.newView) else addToStore(mcDoneStore, mi.missingHead, mi)
    }

    // In each phase below, we also purge all MissingInfos for which the
    // newView has been found, or are done.  In the first two cases, we also
    // purge those whose MissingCommon are done.

    // For each relevant entry in candidateForMCStore, try to match the
    // MissingCommon entries against cv.
    val key = (cv.servers, cv.principal)
    candidateForMCStore.get(key) match{
      case Some(mis) => 
        val newMis = new MissingInfoSet // those to retain
        for(mi <- mis; if !mi.mcDone){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else{
            val vb: ViewBuffer = mi.updateMissingCommon(cv, views)
            if(mi.done) maybeAdd(mi.newView)
            else if(mi.mcDone) mcDone(mi)
            else{
              // Register mi against each view in vb, and retain
              for(cv1 <- vb) addToStore(mcNotDoneStore, cv1, mi)
              newMis += mi
            }
          }
        } // end of for loop
        if(newMis.nonEmpty) candidateForMCStore += key -> newMis
        else candidateForMCStore.remove(key)
      case None => {}
    }

    // Remove cv from the missingViews of the MissingCommon of each entry in
    // mcNotDoneStore.
    mcNotDoneStore.get(cv) match{
      case Some(mis) =>
        mcNotDoneStore.remove(cv) // remove old entry
        for(mi <- mis; if !mi.mcDone){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else{
            val ab = mi.updateMissingViewsOfMissingCommon(cv, views) 
            if(mi.done) maybeAdd(mi.newView) 
            else if(mi.mcDone) mcDone(mi) 
            else for(cv1 <- ab) addToStore(mcNotDoneStore, cv1, mi)
          }
        } // end of for loop
      case None => {}
    }

    // Remove cv from each entry in mcDoneStore.  
    mcDoneStore.get(cv) match{
      case Some(mis) =>
        mcDoneStore.remove(cv) // remove old entry
        for(mi <- mis; if !mi.done){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else{
            mi.updateMissingViewsBy(cv, views)
            if(mi.done) maybeAdd(mi.newView)
            else addToStore(mcDoneStore, mi.missingHead, mi)
          }
        } // end of for loop
      case None => {}
    }

    result
  }

  // def size = (mcDoneStore.size, candidateForMCStore.size)

  /** Check that every stored MissingInfo is either done or contains no element
    * of views. */
  def sanityCheck(views: ViewSet) = {
    println("Sanity check")
    // Do sanity check on all entries of iter.  If flag then they are expected
    // to satisfy mcDone.
    def doCheck(iter: Iterator[Iterable[MissingInfo]], flag: Boolean) = 
      for(mis <- iter; mi <- mis; if !mi.done) mi.sanityCheck(views, flag)
    doCheck(mcDoneStore.valuesIterator, true)
    doCheck(mcNotDoneStore.valuesIterator, false)
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
          // Profiler.count("MissingCommon length "+mi.mcCount)
      (numEls, mvSize, mcSize)
    }
    println
    println("mcDoneStore: size = "+mcDoneStore.size)
    val (storeEls, storeMVSize, storeMCSize) = count(mcDoneStore.valuesIterator)
    println("  # MissingInfos = "+printLong(storeEls))
    println("  MissingInfos missingViews size = "+printLong(storeMVSize))
    println("  MissingInfos missingCommon size = "+printLong(storeMCSize))

    println("candidateForMCStore: size = "+candidateForMCStore.size)
    val (cStoreEls, cStoreMVSize, cStoreMCSize) = 
      count(candidateForMCStore.valuesIterator)
    println("  # MissingInfos = "+printLong(cStoreEls))
    println("  MissingInfos missingViews size = "+printLong(cStoreMVSize))
    println("  MissingInfos missingCommon size = "+printLong(cStoreMCSize))

    println("mcNotDoneStore: size = "+
      mcNotDoneStore.size)
    val (mcmStoreEls, mcmStoreMVSize, mcmStoreMCSize) = 
      count(mcNotDoneStore.valuesIterator)
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
