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

class SimpleEffectOnStore extends EffectOnStore{
  /** A type of stores, giving the MissingInfos that might need updating as the
    * result of finding a new ComponentView. */
  type Store = HashMap[ComponentView, ArrayBuffer[MissingInfo]]

  /** The underlying store concerning missing values.  For each mi: MissingInfo
    * in the abstract set, and for each cv in mi.missingViews, store(cv)
    * contains mi. */
  private val store = new Store
// IMPROVE: replace range by MissingInfoSet

  /** The underlying store concerning MissingCandidates values in missingCommon
    * fields of MissingInfo objects.  For each mi, for each mc in
    * mi.missingCommon, for each cv in mc.missingCandidates.flatten,
    * mcMissingCandidateStore(cv) contains mi. */
  private val mcMissingCandidatesStore = new Store

  /** The underlying store concerning MissingCommon values.  For each mi:
    * MissingInfo in the abstract set, and for each
    * MissingCommon(servers,cpts,_,_) or (servers,_,cpts,_) in
    * mi.missingCommon, commonStore(servers,cpts(0)) contains mi. */
  private val commonStore = new HashMap[(ServerStates, State), List[MissingInfo]]

  /** Add missingInfo to theStore(cv), if not already there. */
  private 
  def addToStore(theStore: Store, cv: ComponentView, missingInfo: MissingInfo)
  = {
    theStore.get(cv) match{
      case Some(ab) => 
        if(!containsAB(ab, missingInfo)) ab += missingInfo
      case None =>
        val ab = new ArrayBuffer[MissingInfo]; ab += missingInfo
        theStore += cv -> ab
    }
  }

  /** Add MissingInfo(nv, missing, missingCommon) to the stores. */
  def add(missing: List[ComponentView], missingCommon: List[MissingCommon], 
    nv: ComponentView)
      : Unit = {
    Profiler.count("EffectOnStore.add")
    val missingInfo = new MissingInfo(nv, missing.toArray, missingCommon.toArray)
    if(missingCommon.isEmpty){
      // Add entries to store
      for(cv <- missing) addToStore(store, cv, missingInfo)
    }
    else{
      // Add entries to mcMissingCandidates
      assert(missingCommon.length <= 1) // FIXME
      for(cv <- missingCommon(0).missingHeads)
        addToStore(mcMissingCandidatesStore, cv, missingInfo)
      // Add entries to commonStore
      for(mc <- missingCommon){
// FIXME: also cpts2? 
        val princ1 = mc.cpts1(0)
        if(false && debugging)
          assert(Remapper.remapToPrincipal(mc.servers, princ1) == princ1)
        val prev = 
          commonStore.getOrElse((mc.servers, princ1), List[MissingInfo]())
        //if(!contains(prev,missingInfo)) // needs equality test
        commonStore += (mc.servers, princ1) -> (missingInfo::prev)
        //else println("Already stored "+missingInfo)
      }
    }
  }

  @inline def containsAB[A](xs: ArrayBuffer[A], x: A): Boolean = {
    var i = 0
    while(i < xs.length && xs(i) != x) i += 1
    i < xs.length
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
    // Update its missingViews; return true if now done; otherwise add to
    // store.
    def mcDone(mi: MissingInfo) = {
      require(mi.mcDone)
      if(mi.updateMissingViews(views)) maybeAdd(mi.newView)
      else for(cv <- mi.missingViews; if cv != null) addToStore(store, cv, mi)
    }

    // In each phase below, we also purge all MissingInfos that are done or
    // for which the newView has been found.

    // For each relevant entry in commonStore, try to match the MissingCommon
    // entries against cv. 
    val key = (cv.servers, cv.principal)
    commonStore.get(key) match{
      case Some(mis) => 
        var newMis = List[MissingInfo]()
        for(mi <- mis; if !mi.done){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else{
            val vb = new ViewBuffer
            if(mi.updateMissingCommon(cv, views, vb)) maybeAdd(mi.newView)
            else if(mi.mcDone) mcDone(mi)
            // IMPROVE: remove from commonStore?
            else{
              // Register mi against each view in vb
              for(cv1 <- vb) addToStore(mcMissingCandidatesStore, cv1, mi)
              newMis ::= mi
            }
          }
          if(newMis.length != mis.length){
            if(newMis.nonEmpty) commonStore += key -> newMis
            else commonStore.remove(key)
          }
        }
      case None => {}
    }

    // Remove cv from the missingViews of the MissingCommon of each entry in
    // mcMissingCandidateStore.
    mcMissingCandidatesStore.get(cv) match{
      case Some(mis) =>
        mcMissingCandidatesStore.remove(cv) // remove old entry
        for(mi <- mis; if !mi.done){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else{
            val ab = mi.updateMCMissingViews(cv, views) 
            if(mi.done) maybeAdd(mi.newView) 
            else if(ab != null)
              for(cv1 <- ab) addToStore(mcMissingCandidatesStore, cv1, mi)
            else mcDone(mi)  // all the MissingCommon entries are satisfied.
          }
        }
      case None => {}
    }

    // Remove cv from each entry in store.  
    store.get(cv) match{
      case Some(mis) =>
        var newMis = new ArrayBuffer[MissingInfo] 
        for(mi <- mis; if !mi.done){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else{
            mi.updateMissingViews(cv)
            if(mi.done) maybeAdd(mi.newView)
            else newMis += mi
          }
        }
        if(newMis.length != mis.length){
          if(newMis.nonEmpty) store += cv -> newMis else store.remove(cv)
        }
      case None => {}
    }

    result
  }

  def size = (store.size, commonStore.size)

  /** Check that every stored MissingInfo is either done or contains no element
    * of views. */
  def sanityCheck(views: ViewSet) = {
    println("Sanity check")
    def doCheck(iter: Iterator[Iterable[MissingInfo]]) = 
      for(mis <- iter; mi <- mis; if !mi.done) mi.sanityCheck(views)
    doCheck(store.valuesIterator)
    doCheck(mcMissingCandidatesStore.valuesIterator)
    doCheck(commonStore.valuesIterator)
  }

  /** Report on size. */
  def report = {
    // The number of MissingInfos in iter, and the sum of their sizes
    def count(iter: Iterator[Iterable[MissingInfo]]): (Long, Long) = {
      // # items in iter, and sum of their sizes
      var numEls = 0L; var elsSize = 0L
      for(mis <- iter; mi <- mis){ numEls += 1; elsSize += mi.size }
          // Profiler.count("MissingCommon length "+mi.mcCount)
      (numEls, elsSize)
    }
    println
    println("store: size = "+store.size)
    val (storeEls, storeElsSize) = count(store.valuesIterator)
    println("  # MissingInfos = "+printLong(storeEls))
    println("  MissingInfos size = "+printLong(storeElsSize))

    println("commonStore: size = "+commonStore.size)
    val (cStoreEls, cStoreElsSize) = count(commonStore.valuesIterator)
    println("  # MissingInfos = "+printLong(cStoreEls))
    println("  MissingInfos size = "+printLong(cStoreElsSize))

    println("mcMissingCandidatesStore: size = "+mcMissingCandidatesStore.size)
    val (mcmStoreEls, mcmStoreElsSize) = 
      count(mcMissingCandidatesStore.valuesIterator)
    println("  # MissingInfos = "+printLong(mcmStoreEls))
    println("  MissingInfos size = "+printLong(mcmStoreElsSize))
    println

    // Find key with largest image
    // val maxKey = store.keys.maxBy(k => store(k).length)
    // println(s"maxKey = $maxKey -> ")
    // for(mi <- store(maxKey)) println(mi)
  }

}
