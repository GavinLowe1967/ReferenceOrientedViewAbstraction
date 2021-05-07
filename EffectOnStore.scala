package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper

/** Objects that record information about which views might be added later.
  * Abstractly it stores tuples (missing, missingCommon, nv) such that:
  * missing is a set of views; missingCommon is a set of (ServerStates, State,
  * State, ProcessIdentity) tuples; and nv is a view.  If
  * 
  * (1) all the views in missing are added; and

  * (2) views are added so all elements of missingCommon satisfy
  * hasCommonRef; i.e. for each (servers, princ1, princ2, pid) in
  * missingCommon, there is a component state c with identity pid such that
  * servers || princ1 || c and servers || princ2 || c are both in sysAbsViews
  * (up to renaming);
  * 
  * then nv can also be added.
  * 
  * These are added in effectOn when a transition are not yet in the store. */ 
trait EffectOnStore{
  /** Each tuple (servers, princ1, princ2, pid): MissingCommon represents a
    * requirement for views servers || princ1 || c and servers || princ2 || c
    * for some component state c with identity pid. */
  type MissingCommon = (ServerStates, State, State, ProcessIdentity)

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
    for((servers,princ1,princ2,_) <- missingCommon; p <- List(princ1, princ2)){
      val pR = Remapper.remapToPrincipal(servers, p) // IMPROVE: only for princ2
      if(p != pR) assert(p != princ1) // IMPROVE
      val prev = commonStore.getOrElse((servers,pR), List[MissingInfo]())
      if(!prev.contains(missingInfo)) 
        commonStore += (servers,pR) -> (missingInfo::prev)
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
