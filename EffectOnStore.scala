package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler

/* Classes in this file record information about when a particular View,
 * newView, can be added, under singleRef.  Each instance arises from a call
 * to EffectOn.apply, but where some views necessary for the compatability of
 * the parameters are not in the ViewSet.  If those required views are
 * subsequently added, we can add newView. */

// /** The representation of the obligation to find a component state c with
//   * identity pid such that (1) servers || cpts1(0) || c is in the ViewSet; (2)
//   * servers || cpts2(0) || c is in the ViewSet; (3) if c has a reference to a
//   * secondary component c2 of cpts1 or cpts2, then servers || c || c2 is in
//   * ViewSet (modulo renaming).  This corresponds to case 2 on p. 113 of the
//   * notebook. */
// class MissingCommon(
//     val servers: ServerStates, val cpts1: Array[State], val cpts2: Array[State],
//     val pid: ProcessIdentity){
//   require(cpts1(0).processIdentities.contains(pid) && 
//     cpts2(0).processIdentities.contains(pid))

//   /** Each value cands of type MissingCandidates represents that if all the
//     * elements of cands are added to the ViewSet, then this obligation will be
//     * discharged. */
//   type MissingCandidates = List[ComponentView]

//   /** When any element of missingCandidates is satisfied, then this obligation
//     * will be discharged. */
//   var missingCandidates = List[MissingCandidates]()

//   override def toString = s"MissingCommon($servers, $cpts1, $cpts2, $pid)"
// }

// =======================================================

/** Information capturing when newView might be added to the ViewSet: once all
  * of missingViews0 have been added, and all the obligations represented by
  * missingCommon0 have been satisfied. */
class MissingInfo(
  val newView: ComponentView, missingViews0: List[ComponentView],
  missingCommon0: List[MissingCommon]
){
  /** Lists of component views necessary to satisfy this constraint: all must be
    * added to the ViewSet.  cf. item 1 on page 113 of notebook. */
  var missingViews: List[ComponentView] = missingViews0

  /** Information about views necessary to satisfy this constraint.  Each
    * represents an obligation to instantiate a component with a particular
    * identity.  cf. item 2 on page 113 of the notebook.  All must be
    * satisfied in order to satisfy this constraint.  */
  var missingCommon: List[MissingCommon] = missingCommon0
// IMPROVE, all the above share the same servers, cpts1, cpts2

  /** Update this, based on new view cv.
    * @return true if all constraints are now satisfied.  */
  def update(cv: ComponentView, views: ViewSet): Boolean = {
    // missingViews = missingViews.filter(v1 => v1 != v && !views.contains(v1))
    var mv = missingViews; missingViews = List[ComponentView]()
    while(mv.nonEmpty){
      val v1 = mv.head; mv = mv.tail
      if(v1 != cv && !views.contains(v1)) 
// IMPROVE: do we need the latter condition?
        missingViews ::= v1
    }

    // missingCommon = missingCommon.filter(!_.update(views))
    var mcs = missingCommon; missingCommon = List[MissingCommon]()
    while(mcs.nonEmpty){
      val mc = mcs.head; mcs = mcs.tail
      if(!mc.update(views)) missingCommon ::= mc
    }

    missingViews.isEmpty && missingCommon.isEmpty
  }

  // def done = missingViews.isEmpty && missingCommon.isEmpty

  override def toString =
    s"MissingInfo($newView, $missingViews0, $missingCommon)"
}

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
  def get(cv: ComponentView): List[MissingInfo]

  def size: (Int, Int)
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

  /** Add MissingInfo(nv, missing, missingCommon) to the store. */
  def add(missing: List[ComponentView], missingCommon: List[MissingCommon], 
    nv: ComponentView)
      : Unit = {
    Profiler.count("EffectOnStore.add")
    val missingInfo: MissingInfo = new MissingInfo(nv, missing, missingCommon)
    for(cv <- missing){
      val prev = store.getOrElse(cv, List[MissingInfo]())
      if(!prev.contains(missingInfo)) store += cv -> (missingInfo::prev)
    }
    for(mc <- missingCommon){
      val princ1 = mc.cpts1(0); val princ2 = mc.cpts2(0)
      for(p <- List(princ1, princ2)){
        val pR = Remapper.remapToPrincipal(mc.servers, p)// IMPROVE: only for princ2
        if(p != pR) assert(p != princ1) // IMPROVE
        val prev = commonStore.getOrElse((mc.servers,pR), List[MissingInfo]())
        if(!prev.contains(missingInfo))
          commonStore += (mc.servers,pR) -> (missingInfo::prev)
      }
    }
  }

  /** Get all pairs (missing, missingCommon, nv) in the store for which cv in
    * relevant. */
  def get(cv: ComponentView): List[MissingInfo] = {
    val mi1 = store.getOrElse(cv, List[MissingInfo]())
    val mi2 =
      commonStore.getOrElse((cv.servers, cv.principal), List[MissingInfo]())
    // if(mi2.nonEmpty) println(s"***$cv -> $mi1,\n  ${mi2.mkString("\n  ")}")
    append1(mi1,mi2)
// IMPROVE if latter empty
  }


  def size = (store.size, commonStore.size)
}
