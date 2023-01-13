package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper
import collection.{OpenHashSet,ShardedHashMap}
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
  def add(missing: Array[ReducedComponentView], 
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
  /** Show an induced transition.  Used in SingleRefEffectOn.tryAddNewView. */
  def showInduced(cv: ComponentView0, oldCpts: Array[State], 
    postServers: ServerStates, newCpts: Array[State], nv: ReducedComponentView)
      : String = {
    // assert(oldCpts.map(_.cs).sameElements(cv.components.map(_.cs)))
    s"$cv\n"+
      (if(!cv.components.sameElements(oldCpts))
        s"  == ${View.show(cv.servers, oldCpts)}\n"
      else "")+
      s"  --> ${View.show(postServers, newCpts)}\n"+
      (if(postServers != nv.servers || !newCpts.sameElements(nv.components))
        s"  ==  $nv"
      else "")
  }
  // Note, the above can look odd when cv changes state in the transition, and
  // the induced transition gets a new secondary component.  Maybe it's
  // possible to avoid these cases.  Also it looks odd for secondary induced
  // transitions.

  // private var theStore: EffectOnStore = null

  // def set(store: EffectOnStore)


}
