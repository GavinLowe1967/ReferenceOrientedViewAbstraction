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
  // It will be unusual for the list to contain more than one element, I think. 
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
    var mcs = missingCommon; missingCommon = List() 
    while(mcs.nonEmpty){
      val mc = mcs.head; mcs = mcs.tail
      if(!mc.update(views)) missingCommon ::= mc
    }
// IMPROVE: pass cv to mc.update, and test whether this allows a new component.
    missingViews.isEmpty && missingCommon.isEmpty
  }

  def done = missingViews.isEmpty && missingCommon.isEmpty

  import MissingCommon.ViewBuffer

  /** Update the MissingCommon entries in this, based on cv being a possible
    * match to the first clause of the obligation.  Pre: cv is a possible
    * match to at least one.  Add to ab all Views that this needs to be
    * registered against in the store. */
  def updateMC(cv: ComponentView, views: ViewSet, ab: ViewBuffer) = {
    var matched = false // have we found a MissingCommon entry that matches?
    var mcs = missingCommon; missingCommon = List()
    while(mcs.nonEmpty){
      val mc = mcs.head; mcs = mcs.tail
      if(mc.matches(cv)){
        matched = true
        if(!mc.updateMC(cv, views, ab)) missingCommon ::= mc
        else println(s"Removed $mc from $this")
      }
    }
// FIXME: add following: not true when also using update
    //assert(matched, s"\nupdateMC($cv):\n  $missingCommon")

    // Profiler.count(s"updateMC"+missingCommon.length) // Never seen more than 1

    // Find those ComponentViews with which this has to be registered in the
    // store.
    // if(missingCommon.isEmpty) ArrayBuffer[ComponentView]()
    // else if(missingCommon.length == 1) missingCommon.head.getToRegister
    // else{
    //   // Expensive but rare case; improve?
    //   val ab = missingCommon.head.getToRegister
    //   for(mc <- missingCommon.tail) ab ++= mc.getToRegister
    //   ab
    // } 
  }


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

  private def addToStore(cv: ComponentView, missingInfo: MissingInfo) = {
    val prev = store.getOrElse(cv, List[MissingInfo]())
    if(!prev.contains(missingInfo)) store += cv -> (missingInfo::prev)
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
      val princ1 = mc.cpts1(0) // ; val princ2 = mc.cpts2(0)
      if(debugging)
        assert(Remapper.remapToPrincipal(mc.servers, princ1) == princ1)
      val prev = commonStore.getOrElse((mc.servers, princ1), List[MissingInfo]())
      if(!prev.contains(missingInfo))
        commonStore += (mc.servers, princ1) -> (missingInfo::prev)
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

  import MissingCommon.ViewBuffer

  /** Try to complete values in the store, based on the addition of cv, and with
    * views as the ViewSet.  Return the MissingInfo that are now complete.  */
  def complete(cv: ComponentView, views: ViewSet): List[MissingInfo] = {
    var result = List[MissingInfo]()
    val mis: List[MissingInfo] = 
      commonStore.getOrElse((cv.servers, cv.principal), List[MissingInfo]())
    for(mi <- mis){
      val vb = new ViewBuffer; mi.updateMC(cv, views, vb)
      if(mi.done){
        println(s"$mi complete")
        result ::= mi
// IMPROVE: remove mi from mapping
      }
      else{
        // Register mi against each view in vb
        for(cv1 <- vb){
          // println(s"Adding $cv1 -> $mi")
          addToStore(cv1, mi)
        }
      }
    }
// Remove cv from each entry in store
    result
  }


  def size = (store.size, commonStore.size)
}
