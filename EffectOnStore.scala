package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashMap}

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
  /** The underlying store concerning missing values.  For each mi: MissingInfo
    * in the abstract set, and for each cv in mi.missingViews, store(cv)
    * contains mi. */
  private val store = new HashMap[ComponentView, List[MissingInfo]]

  /** The underlying store concerning MissingCommon values.  For each mi:
    * MissingInfo in the abstract set, and for each
    * MissingCommon(servers,cpts,_,_) or (servers,_,cpts,_) in
    * mi.missingCommon, commonStore(servers,cpts(0)) contains mi. */
  private val commonStore = new HashMap[(ServerStates, State), List[MissingInfo]]

  private def addToStore(cv: ComponentView, missingInfo: MissingInfo) = {
    val prev = store.getOrElse(cv, List[MissingInfo]())
    if(!prev.contains(missingInfo))
      store += cv -> (missingInfo::prev)
    // else println("Already stored "+missingInfo)
  }

  /** Add MissingInfo(nv, missing, missingCommon) to the store. */
  def add(missing: List[ComponentView], missingCommon: List[MissingCommon], 
    nv: ComponentView)
      : Unit = {
    Profiler.count("EffectOnStore.add")
    val missingInfo = new MissingInfo(nv, missing.toArray, missingCommon.toArray)
    for(cv <- missing) addToStore(cv, missingInfo)
    for(mc <- missingCommon; cv <- mc.allCandidates) addToStore(cv, missingInfo)
    for(mc <- missingCommon){
      val princ1 = mc.cpts1(0)
      if(false && debugging)
        assert(Remapper.remapToPrincipal(mc.servers, princ1) == princ1)
      val prev = commonStore.getOrElse((mc.servers, princ1), List[MissingInfo]())
      //if(!contains(prev,missingInfo)) // needs equality test
        commonStore += (mc.servers, princ1) -> (missingInfo::prev)
      //else println("Already stored "+missingInfo)
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

    // For each relevant entry in commonStore, try to match the MissingCommon
    // entries against cv.  We also purge all MissingInfos that are done or
    // for which the newView has been found.
    val key = (cv.servers, cv.principal)
    commonStore.get(key) match{
      case Some(mis) => 
        var newMis = List[MissingInfo]()
        for(mi <- mis; if !mi.done){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else{
            val vb = new ViewBuffer
            if(mi.updateMissingCommon(cv, views, vb)) maybeAdd(mi.newView)
            else{
              // Register mi against each view in vb
              for(cv1 <- vb) addToStore(cv1, mi)
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

    // Remove cv from each entry in store.  We also purge all MissingInfos
    // that are done or for which the newView has been found.
    store.get(cv) match{
      case Some(mis) =>
        var newMis = List[MissingInfo]()
        for(mi <- mis; if !mi.done){
          if(views.contains(mi.newView)) mi.markNewViewFound
          else if(mi.updateMissingViews(cv)) maybeAdd(mi.newView)
          else newMis ::= mi
        }
        // Profiler.count("store changed"+(newMis.length == mis.length))
        // Profiler.count("EffectOnStore"+newMis.length)
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
    for(mis <- store.valuesIterator; mi <- mis; if !mi.done){
      mi.sanityCheck(views)
    }
  }

  /** Report on size. */
  def report = {
    println
    println("store.size = "+store.size)
    // # items in store, and sum of their sizes
    var storeEls = 0L; var storeElsSize = 0L
    for(mis <- store.valuesIterator){
      storeEls += mis.length
      for(mi <- mis) storeElsSize += mi.size
    }
    println("store # MissingInfos = "+printLong(storeEls))
    println("store MissingInfos size = "+printLong(storeElsSize))
    println("commonStore.size = "+commonStore.size)
    // Find key with largest image
    // val maxKey = store.keys.maxBy(k => store(k).length)
    // println(s"maxKey = $maxKey -> ")
    // for(mi <- store(maxKey)) println(mi)
  }

}
