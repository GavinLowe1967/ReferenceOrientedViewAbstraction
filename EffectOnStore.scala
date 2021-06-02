package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.ArrayBuffer

/* Classes in this file record information about when a particular View,
 * newView, can be added, under singleRef.  Each instance arises from a call
 * to EffectOn.apply, but where some views necessary for the compatability of
 * the parameters are not in the ViewSet.  If those required views are
 * subsequently added, we can add newView. */

// =======================================================

// /** Information capturing when newView might be added to the ViewSet: once all
//   * of missingViews0 have been added, and all the obligations represented by
//   * missingCommon0 have been satisfied. */
// class MissingInfo(
//   val newView: ComponentView, missingViews0: List[ComponentView],
//   missingCommon0: List[MissingCommon]
// ){
//   /** Lists of component views necessary to satisfy this constraint: all must be
//     * added to the ViewSet.  cf. item 1 on page 113 of notebook. */
//   var missingViews: List[ComponentView] = missingViews0

//   /** Information about views necessary to satisfy this constraint.  Each
//     * represents an obligation to instantiate a component with a particular
//     * identity.  cf. item 2 on page 113 of the notebook.  All must be
//     * satisfied in order to satisfy this constraint.  */
//   var missingCommon: List[MissingCommon] = missingCommon0
//   // It will be unusual for the list to contain more than one element, I think. 
// // IMPROVE, all the above share the same servers, cpts1, cpts2

//   def done = missingViews.isEmpty && missingCommon.isEmpty

//   import MissingCommon.ViewBuffer

//   /** Update the MissingCommon entries in this, based on cv being a possible
//     * match to the first clause of the obligation.  Add to ab all Views that
//     * this needs to be registered against in the store.  cv is expected to be
//     * a possible match to at least one member of missingCommon0. 
//     * @return true if this is now complete. */
//   def updateMissingCommon(cv: ComponentView, views: ViewSet, ab: ViewBuffer)
//       : Boolean = {
//     var matched = false // have we found a MissingCommon entry that matches?
//     var mcs = missingCommon; missingCommon = List()
//     while(mcs.nonEmpty){
//       val mc = mcs.head; mcs = mcs.tail
//       if(mc.matches(cv)){
//         matched = true
//         if(!mc.updateMissingCommon(cv, views, ab)) missingCommon ::= mc
//         // else println(s"Removed $mc from $this")
//       }
//       else missingCommon ::= mc
//     }
//     if(debugging && !matched) // check precondition
//       assert(missingCommon0.exists(mc => mc.matches(cv)),
//         s"\nupdateMC($cv):\n  $missingCommon\n $missingCommon0")
//     done
//   }

//   /** Update this based on the addition of cv.  cv is expected to match a
//     * missing view that was added to missingViews or missingCommon (maybe
//     * subsequently removed).
//     * @return true if this is now complete. */
//   def updateMissingViews(cv: ComponentView): Boolean = {
//     // Remove cv from each element of missingCommon.
//     var mcs = missingCommon; missingCommon = List()
//     while(mcs.nonEmpty){
//       val mc = mcs.head; mcs = mcs.tail
//       if(! mc.updateMissingViews(cv)) missingCommon ::= mc
//     }

//     // Remove cv from missingViews
//     var mvs = missingViews; missingViews = List()
//     while(mvs.nonEmpty){
//       val mv = mvs.head; mvs = mvs.tail
//       if(mv != cv) missingViews ::= mv
//     }

//     done
//   }
// // IMPROVE: maybe EffectOnStore should store MissingInfos separately,
// // depending on which of the phases of update1 is relevant.

//   /** Check that this contains no element of views remains in missingViews. */
//   def sanityCheck(views: ViewSet) = {
//     assert(!done)
//     for(v <- missingViews) assert(!views.contains(v))
//     for(mc <- missingCommon) mc.sanityCheck(views)
//   }

//   override def toString =
//     s"MissingInfo($newView, $missingViews0, $missingCommon0)"

//   override def equals(that: Any) = that match{
//     case mi: MissingInfo => 
//       mi.newView == newView && mi.missingViews == missingViews &&
//       mi.missingCommon == missingCommon
//   }

//   def size = missingViews.length + missingCommon.map(_.size).sum
// }

// =======================================================

/** Objects that record information about which views might be added later.
  * Abstractly it stores a set of MissingInfo objects.
  * 
  * These are added in effectOn when a transition are not yet in the store. */ 
trait EffectOnStore{

  /** Add MissingInfo(nv, missing, missingCommon) to the store. */
  def add(missing: List[ComponentView], missingCommon: List[MissingCommon], 
    nv: ComponentView): Unit

  /** Get all MissingInfo values in the store for which cv is relevant: either
    * cv is in missingViews, or in an element of
    * missingCommon.missingCandidates, or ........ . */
  // def get(cv: ComponentView): List[MissingInfo]

  /** Try to complete values in the store, based on the addition of cv, and with
    * views as the ViewSet.  Return the Views that can now be added.  */
  def complete(cv: ComponentView, views: ViewSet): List[ComponentView]

  /** Sanity check performed at the end of a run. */
  def sanityCheck(views: ViewSet): Unit

  def size: (Int, Int)

  def report: Unit
}

// =======================================================

import scala.collection.mutable.HashMap

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
    //if(!prev.contains(missingInfo))
    store += cv -> (missingInfo::prev)
  }

  /** Add MissingInfo(nv, missing, missingCommon) to the store. */
  def add(missing: List[ComponentView], missingCommon: List[MissingCommon], 
    nv: ComponentView)
      : Unit = {
    Profiler.count("EffectOnStore.add")
    val missingInfo: MissingInfo = new MissingInfo(nv, missing, missingCommon)
    for(cv <- missing) addToStore(cv, missingInfo)
    for(mc <- missingCommon; cv <- mc.allCandidates) addToStore(cv, missingInfo)
    for(mc <- missingCommon){
      val princ1 = mc.cpts1(0)
      if(false && debugging)
        assert(Remapper.remapToPrincipal(mc.servers, princ1) == princ1)
      val prev = commonStore.getOrElse((mc.servers, princ1), List[MissingInfo]())
      // if(!contains(prev,missingInfo)) // needs equality test
      commonStore += (mc.servers, princ1) -> (missingInfo::prev)
      // else println("Already stored "+missingInfo)
    }
  }

  private def contains(cvs: List[MissingInfo], cv: MissingInfo): Boolean = 
    cvs.nonEmpty && (cvs.head == cv || cvs.tail.contains(cv))

  /** Get all pairs (missing, missingCommon, nv) in the store for which cv in
    * relevant. */
//   def get(cv: ComponentView): List[MissingInfo] = { ???
//     val mi1 = store.getOrElse(cv, List[MissingInfo]())
//     val mi2 =
//       commonStore.getOrElse((cv.servers, cv.principal), List[MissingInfo]())
//     // if(mi2.nonEmpty) println(s"***$cv -> $mi1,\n  ${mi2.mkString("\n  ")}")
//     append1(mi1,mi2)
// // IMPROVE if latter empty
//   }

  import MissingCommon.ViewBuffer

  /** Try to complete values in the store, based on the addition of cv, and with
    * views as the ViewSet.  Return the Views that can now be added.  */
  def complete(cv: ComponentView, views: ViewSet): List[ComponentView] = {
    var result = List[ComponentView]()
    // Add nv to result if not already there
    def maybeAdd(nv: ComponentView) = if(!result.contains(nv)) result ::= nv

    // For each relevant entry in commonStore, try to match the MissingCommon
    // entries against cv.
    val mis: List[MissingInfo] = 
      commonStore.getOrElse((cv.servers, cv.principal), List[MissingInfo]())
    for(mi <- mis; if !mi.done){
      val vb = new ViewBuffer; 
      if(mi.updateMissingCommon(cv, views, vb)) maybeAdd(mi.newView)
      else // Register mi against each view in vb
        for(cv1 <- vb) addToStore(cv1, mi)
    }

    // Remove cv from each entry in store
    val mis2 = store.getOrElse(cv, List[MissingInfo]())
    for(mi <- mis2; if !mi.done){
      if(mi.updateMissingViews(cv)) maybeAdd(mi.newView) 
    }
    result
  }
  // Note: there seems to be a lot of repeated work above, reconsidering
  // MissingInfos for which the view is already in views.  Maybe remove
  // entries, and/or check whether the corresponding newView is already in
  // views, earlier. IMPROVE


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
    var storeEls = 0; var storeElsSize = 0
    for(mis <- store.valuesIterator){
      storeEls += mis.length
      for(mi <- mis) storeElsSize += mi.size
    }
    println("store # MissingInfos = "+storeEls)
    println("store MissingInfos size = "+storeElsSize)
    println("commonStore.size = "+commonStore.size)
  }

}
