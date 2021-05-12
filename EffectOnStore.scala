package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper

/* Classes in this file record information about when a particular View,
 * newView, can be added, under singleRef.  Each instance arises from a call
 * to EffectOn.apply, but where some views necessary for the compatability of
 * the parameters are not in the ViewSet.  If those required views are
 * subsequently added, we can add newView. */

/** The representation of the obligation to find a component state c with
  * identity pid such that (1) servers || cpts1(0) || c is in the ViewSet; (2)
  * servers || cpts2(0) || c is in the ViewSet; (3) if c has a reference to a
  * secondary component c2 of cpts1 or cpts2, then servers || c || c2 is in
  * ViewSet (modulo renaming).  This corresponds to case 2 on p. 113 of the
  * notebook. */
class MissingCommonX(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State],
    pid: ProcessIdentity){
  require(cpts1(0).processIdentities.contains(pid) && 
    cpts2(0).processIdentities.contains(pid))

  /** Each value cands of type MissingCandidates represents that if all the
    * elements of cands are added to the ViewSet, then this obligation will be
    * discharged. */
  type MissingCandidates = List[ComponentView]

  /** When any element of missingCandidates is satisfied, then this obligation
    * will be discharged. */
  var missingCandidates = List[MissingCandidates]()
}

// =======================================================

/** Information capturing when newView might be added to the ViewSet, once
  * other views have also been encountered. */
class MissingInfoX(
  val newView: ComponentView, missingViews0: List[ComponentView],
  missingCommon0: List[MissingCommonX]
){
  /** Lists of component views necessary to satisfy this constraint: all must be
    * added to the ViewSet.  cf. item 1 on page 113 of notebook. */
  var missingViews: List[ComponentView] = missingViews0

  /** Information about views necessary to satisfy this constraint.  Each
    * represents an obligation to instantiate a component with a particular
    * identity.  cf. item 2 on page 113 of the notebook.  All must be
    * satisfied in order to satisfy this constraint.  */
  var missingCommon: List[MissingCommonX] = missingCommon0
// IMPROVE, all the above share the same servers, cpts1, cpts2
}

// =======================================================

/** Objects that record information about which views might be added later.
  * Abstractly it stores tuples (missing, missingCommon, nv) such that:
  * missing is a set of views; missingCommon is a set of (ServerStates, State,
  * State, ProcessIdentity) tuples; and nv is a view.  If
  * 
  * (1) all the views in missing are added; and
  * 
  * (2) views are added so all elements of missingCommon satisfy
  * hasCommonRef; i.e. for each (servers, cmpts1, cmpts2, pid) in
  * missingCommon, there is a component state c with identity pid such that
  * each of the following is in sysAbsViews (up to renaming): (1) servers ||
  * cmpts1(0) || c; (2) servers || cmpts2(0) || c; and servers || c || c2 for
  * any secondary component c2 referenced by c.
  * 
  * then nv can also be added.
  * 
  * These are added in effectOn when a transition are not yet in the store. */ 
trait EffectOnStore{
  /** Each tuple (servers, princ1, princ2, pid): MissingCommon represents a
    * requirement for views servers || princ1 || c and servers || princ2 || c
    * for some component state c with identity pid. */
// IMPROVE COMMENT
  type MissingCommon = 
    (ServerStates, Array[State], Array[State], ProcessIdentity)

  /** Add the tuple (missing, missingCommon, nv) to the store. */
  def add(missing: List[ComponentView], missingCommon: List[MissingCommon], 
    nv: ComponentView): Unit

  type MissingInfo = (List[ComponentView], List[MissingCommon], ComponentView)

  /** Get all tuples (missing, missingCommon, nv) in the store for which cv is
    * relevant: either cv is in missing, or matches an element of
    * missingCommon. */
  def get(cv: ComponentView): List[MissingInfo]

  def size: (Int, Int)
}

// =======================================================

import scala.collection.mutable.HashMap

class SimpleEffectOnStore extends EffectOnStore{
  /** The underlying store concerning missing values.  For each tuple (missing,
    * missingCommon, nv) in the abstract set, and for each cv in missing,
    * store(cv) contains (missing, missingCommon, nv). */
  private val store = new HashMap[ComponentView, List[MissingInfo]]

  /** The underlying store concerning MissingCommon values.  For each tuple
    * (missing, missingCommon, nv) in the abstract set, and for each
    * (servers,princ,_,_) or (servers,_,princ,_) in missingCommon, commonStore
    * contains (servers,princ) -> (missing, missingCommon, nv). */
  private val commonStore = new HashMap[(ServerStates, State), List[MissingInfo]]

  /** Add the pair (missing, missingCommon, nv) to the store. */
  def add(missing: List[ComponentView], missingCommon: List[MissingCommon], 
    nv: ComponentView)
      : Unit = {
    val missingInfo: MissingInfo = (missing,missingCommon,nv)
    for(cv <- missing){
      val prev = store.getOrElse(cv, List[MissingInfo]())
      if(!prev.contains(missingInfo)) store += cv -> (missingInfo::prev)
    }
    for((servers,cpts1,cpts2,_) <- missingCommon){
      val princ1 = cpts1(0); val princ2 = cpts2(0)
      for(p <- List(princ1, princ2)){
        val pR = Remapper.remapToPrincipal(servers, p)// IMPROVE: only for princ2
        if(p != pR) assert(p != princ1) // IMPROVE
        val prev = commonStore.getOrElse((servers,pR), List[MissingInfo]())
        if(!prev.contains(missingInfo))
          commonStore += (servers,pR) -> (missingInfo::prev)
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
