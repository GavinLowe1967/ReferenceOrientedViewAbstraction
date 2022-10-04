package ViewAbstraction

import collection.MyHashSet
import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}

/** Object to calculate the effect of the transition trans on cv.  Create
  * extra views caused by the way the transition changes cv, and add them to
  * nextNewViews. */
class EffectOn(
  trans: Transition, cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
{
  /* Overview of main function.
   * 
   * apply
   * |--getCrossReferences
   * |--EffectOnUnification.apply/SingleRefEffectOnUnification.apply
   * |--processInduced
   * |  |--getCrossRefs
   * |  |--processInducedInfoFullViews
   * |--processInducedSingleRef
   * |  |-processInducedInfo
   * |     |--processInducedInfoSingleRef
   * |     |  |--checkCompatibleMissing
   * |     |  |--EffectOn.effectOnStore.add
   * |     |--processInducedInfoNewEffectOnStore
   * |        |--missingCrossRefs
   * |        |--EffectOn.commonMissingRefs
   * |        |--EffectOn.effectOnStore.add
   * |--processSecondaryInduced
   * |  |--getCrossRefs
   * |  |--processInducedInfo (as above)
   */

  //import EffectOn.{getCrossRefs,commonMissingRefs}

  import Unification.UnificationList //  = List[(Int,Int)]

  import ServersReducedMap.ReducedMap 

  import SingleRefEffectOnUnification.{InducedInfo, SecondaryInducedInfo}

  import RemappingExtender.Linkage

  // InducedInfo = 
  //   ArrayBuffer[(RemappingMap, Array[State], UnificationList, ReducedMap)]
  // SecondaryInducedInfo = ArrayBuffer[(Array[State], UnificationList, Int)]

  protected val pre = trans.pre; protected val post = trans.post
  protected val postCpts = post.components;

  private val highlight = 
    Transition.highlight(trans) && {
      // [107(N0) || 109(N1) || 110() || 114(T0) || 119() || 1()] ||
      // [31(T1,N2,N3,N1) || 10(N2,Null,N3)]
      val princ = cv.components(0)
      princ.cs == 31 && princ.ids.sameElements(Array(1,2,3,1)) && {
        val second = cv.components(1)
        second.cs == 10 && second.ids.sameElements(Array(2,-1,3))
      }
    }

  if(highlight) println(s"\nEffectOn($trans,\n  $cv)")

  require(pre.servers == cv.servers) // && pre.sameComponentPids(post)

  override def toString = s"EffectOn($trans, $cv)"

  /** What does cpt get mapped to given unifications unifs? */
  protected def getNewPrinc(cpt: State, unifs: UnificationList): State = {
    var us = unifs; while(us.nonEmpty && us.head._1 != 0) us = us.tail
    if(us.isEmpty) cpt else postCpts(us.head._2)
  }
  
  import EffectOn.views

  protected var sreou: SingleRefEffectOnUnification = null

  /** The effect of the transition t on cv.  Create extra views caused by the
    * way the transition changes cv, and add them to nextNewViews. */
  def apply() : Unit = {
    // Early bail-out if servers don't change, no chance of unification with
    // components that change state, and no chance of secondary induced
    // transitions.  This captures over about 25% of cases with lazySet.csp,
    // bound 44; nearly all other cases have servers that change state.
    if(trans.mightGiveSufficientUnifs(cv)){
      // inducedInfo: ArrayBuffer[(RemappingMap, Array[State],
      // UnificationList, ReducedMap)] is a set of tuples (pi, pi(cv.cpts),
      // unifs, reducedMap) where pi is a unification function corresponding
      // to unifs.
      val inducedInfo: EffectOnUnification.InducedInfo =
        EffectOnUnification.combine(trans, cv)
      processInduced(inducedInfo)
    }
  }

  /** Process the information about induced transitions with full views. */
  @inline private 
  def processInduced(inducedInfo: EffectOnUnification.InducedInfo) = {
    require(!singleRef); var index = 0
    while(index < inducedInfo.length){
      val (map, unifs) = inducedInfo(index); index += 1
      Profiler.count("EffectOn step "+unifs.isEmpty)
      val cpts = Remapper.applyRemapping(map, cv.components)
      val newPrinc = getNewPrinc(cpts(0), unifs)
      var newComponentsList =
        StateArray.makePostComponents(newPrinc, postCpts, cpts)
      processInducedInfoFullViews(cpts, unifs, newComponentsList)
      Pools.returnRemappingRows(map)
    } // end of while loop
  }

  /** Make cpts, by applying map to cv.components.  If useNewEffectOnStore, map
    * undefined values in map to fresh values. */
  @inline protected def mkComponents(map: RemappingMap): Array[State] = 
    if(useNewEffectOnStore){
      val map1 = Remapper.cloneMap(map)
      Remapper.mapUndefinedToFresh(map1, trans.getNextArgMap)
      val cs = Remapper.applyRemapping(map1, cv.components)
      Pools.returnRemappingRows(map1); cs
    }
    else Remapper.applyRemapping(map, cv.components)

  // ---------- Helper functions for the processInduced functions

  /** Record this induced transition if singleRef and primary, and (1) if
   ** newEffectOn, no acquired references, (2) otherwise no unifs. */
  @inline protected
  def recordInduced(unifs: UnificationList, reducedMap: ReducedMap) = {
    assert(singleRef) // && isPrimary
    // IMPROVE: repeats work from SingleRefEffectOnUnification:
    // doesPrincipalAcquireRef and getPostUnified.
    if(StoreDoneInducedPostServersRemaps){ // currently true
      if(DetectRepeatRDMapWithUnification){ // currently false
        if(!trans.doesPrincipalAcquireRef(unifs))
          cv.addDoneInducedPostServersRemaps(post.servers, reducedMap,
            trans.getPostUnified(unifs, cv.components.length) )
      }
      else if(unifs.isEmpty) // current version
        cv.addDoneInducedPostServersRemaps(post.servers, reducedMap)
    }
    // Record that we've done a transition on cv with these post servers
    // and no unifications
    if(!trans.isChangingUnif(unifs) && !trans.serverGetsNewId)
      cv.addDoneInduced(post.servers)
  }

  /** Actions performed when a new view has been added to the view set,
    * principally setting the creation information. */
  @inline protected def addedView(
    cpts: Array[State], newComponents: Array[State], nv: ComponentView,
    unifs: UnificationList, isPrimary: Boolean, reducedMap: ReducedMap)
  = {
    if(highlight) println("added")
    Profiler.count("addedViewCount")
    if(showTransitions || ComponentView0.highlight(nv))
      showTransition(cpts, newComponents, nv, unifs, isPrimary)
    nv.setCreationInfoIndirect(trans, cpts, cv, newComponents)
    if(singleRef && isPrimary) recordInduced(unifs, reducedMap)
    checkRepresentable(nv)
  }

  /** Process induced information in the case of full views. */
  private def processInducedInfoFullViews(
    cpts: Array[State], unifs: UnificationList, // reducedMap: ReducedMap, 
    newComponentsList: List[Array[State]])
      : Unit = {
    require(!singleRef)
    for(newComponents <- newComponentsList){
      val nv = Remapper.mkComponentView(post.servers, newComponents)
      Profiler.count("newViewCount") 
      if(!views.contains(nv)){
        if(nextNewViews.add(nv))
          addedView(cpts, newComponents, nv, unifs, true, null/*reducedMap*/)
        else // nv was in nextNewViews 
          showRedundancy(
            nextNewViews.get(nv), cpts, newComponents, nv, unifs, true)
      } // end of if(!views.contains(nv))
      // Try to work out why so many cases are redundant
      else // views already contains nv
        showRedundancy(views.get(nv), cpts, newComponents, nv, unifs, true)
    } // end of for loop
  }


  // ----------- Various helper functions

  /** Show the transition. */
  @inline private def showTransition(
    cpts: Array[State], newComponents: Array[State], nv: ComponentView, 
    unifs: UnificationList, isPrimary: Boolean)
  = println(s"$trans\n  with unifications $unifs, isPrimary == $isPrimary\n"+
    "  induces "+
    EffectOnStore.showInduced(cv, cpts, post.servers, newComponents, nv)
  )

  /** Show information about a redundancy. */
  @inline protected def showRedundancy(
    v1: => ComponentView, cpts: Array[State], newComponents: Array[State], 
    nv: ComponentView, unifs: UnificationList, isPrimary: Boolean)
  = {
    Profiler.count("EffectOn redundancy:"+isPrimary+unifs.isEmpty)
    if(showRedundancies && v1.inducedFrom(cv)){
      showTransition(cpts, newComponents, nv, unifs, isPrimary)
      println(s"Previously "+v1.showCreationInfo+"\n")
    }
  }

  /** Check that nv is representable using the identities in the script. */
  @inline private def checkRepresentable(nv: ComponentView) = 
    if(!nv.representableInScript){
      println("Not enough identities in script to combine transition\n"+
        s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
      sys.exit()
    }
}

// ==================================================================


/** Supporting functions for EffectOn objects, and encapsulation of the
  * EffectOnStore. */
object EffectOn{
  /** The current set of views.  Set by init. */
  var views: ViewSet = null
// IMPROVE: protect

  /** The system.  Set by init. */
  private var system: SystemP.System = null

  def init(views: ViewSet, system: SystemP.System) = {
    this.views = views; this.system = system
  }

  /* Overview of main functions.
   * 
   * completeDelayed
   * |--EffectOnStore.complete
   * |--tryAddNewView 
   * 
   * getCrossRefs
   * |--StateArray.crossRefs
   * 
   * reset, prepareForPurge, purge, sanityCheck, report, memoryProfile
   */

  // /** A mapping showing which component views might be added later.
  //   * Abstractly it stores tuples (missing, missingCommon, nv) such that:
  //   * missing is a set of views; missingCommon is a set of (ServerStates, State,
  //   * State, ProcessIdentity) tuples; and nv is a view.  If
  //   * 
  //   * (1) all the views in missing are added; and
  //   * 
  //   * (2) views are added so all elements of missingCommon satisfy
  //   * hasCommonRef; i.e. for each (servers, princ1, princ2, pid) in
  //   * missingCommon, there is a component state c with identity pid such that
  //   * servers || princ1 || c and servers || princ2 || c are both in sysAbsViews
  //   * (up to renaming);
  //   * 
  //   * then nv can also be added.
  //   * 
  //   * Tuples are added to the store in apply when a transition is prevented
  //   * because relevant views are not yet in the store.  completeDelayed
  //   * subsequently tries to complete the transitions.  */
  // var effectOnStore: EffectOnStore = 
  //   if(singleRef && !useNewEffectOnStore) new SimpleEffectOnStore else null

  // var newEffectOnStore: NewEffectOnStore =
  //   if(singleRef && useNewEffectOnStore) new NewEffectOnStore else null

  // def reset = { 
  //   if(singleRef){
  //     if(useNewEffectOnStore) newEffectOnStore = new NewEffectOnStore
  //     else effectOnStore = new SimpleEffectOnStore
  //   }
  //   //lastPurgeViewCount = 0L; doPurge = false
  // }

  // import Unification.UnificationList //  = List[(Int,Int)]

  // import ServersReducedMap.ReducedMap 

  // private def highlight(cv: ComponentView) =
  //   ComponentView0.highlightServers(cv.servers) && 
      // //  44(T2,N5,N6) or 45(T2,N5,N6)
      // ComponentView0.highlightPrinc(cv.components(0)) && {
      //   val second = cv.components(1)
      //   // 16|17(N6,_,N4,N2)
      //   (second.cs == 17 || second.cs == 16) &&
      //   second.ids(0) == 5 && second.ids(2) == 3 && second.ids(3) == 1
      // }

  // /** If cv completes a delayed transition in effectOnStore, then complete it. */
  // def completeDelayed(cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
  // = {
  //   val newViews =
  //     if(useNewEffectOnStore) newEffectOnStore.complete(cv, views)
  //     else effectOnStore.complete(cv, views)
  //   // if(highlight(cv)) println(s"completeDelayed($cv)")
  //   for(nv <- newViews){
  //     if(showTransitions || ComponentView0.highlight(nv)) 
  //       println(s"Adding $nv\n from completeDelayed($cv)")
  //     tryAddView(nv, nextNewViews)
  //   }
  // }

  // /** Add mi.nextNewViews to nextNewViews. */
  // @inline private 
  // def tryAddView(nv: ComponentView, nextNewViews: MyHashSet[ComponentView]) = {
  //   // require(mi.done); val nv = mi.newView
  //   if(nextNewViews.add(nv)){
  //     if(showTransitions || ComponentView0.highlight(nv)){
  //       val (trans, cpts, cv, newComponents) = nv.getCreationIngredients
  //       println(s"Adding via completeDelayed \n"+
  //         s"$trans induces \n"+
  //         EffectOnStore.showInduced(
  //           cv, cpts, trans.post.servers, newComponents, nv))
  //     }
  //     if(!nv.representableInScript){
  //       val (trans, cpts, cv, newComponents) = nv.getCreationIngredients
  //       println("Not enough identities in script to combine transition\n"+
  //         s"$trans and\n$cv.  Produced view\n"+nv.toString0)
  //       sys.exit()
  //     }
  //   } // end of outer if
  // }

  // /** Get (the components of) the cross reference views between cpts1 and cpts2,
  //   * needed for condition (b). */
  // @inline def getCrossRefs(
  //   servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
  //     : List[Array[State]] = {
  //   assert(singleRef)
  //   StateArray.crossRefs(cpts1, cpts2).map(Remapper.remapComponents(servers,_))
  // }

  // /** Get (the components of) the cross reference views between map(cpts1) and
  //   * cpts2, needed for condition (b).  map might be undefined on some
  //   * components of cpts1: only consider those states of cpts1 where the map
  //   * is fully defined. */
  // @inline private def getCrossRefs1(servers: ServerStates, 
  //   cpts1: Array[State], cpts2: Array[State], map: RemappingMap)
  //     : List[Array[State]] = {
  //   val cpts1Renamed = 
  //     cpts1.filter(Remapper.isDefinedOver(map, _)).
  //       map(Remapper.applyRemappingToState(map,_))
  //   getCrossRefs(servers, cpts1Renamed, cpts2)
  // }

  // /** All common included missing references from cpts1 and cpts2. */
  // @inline def commonMissingRefs(cpts1: Array[State], cpts2: Array[State])
  //     : List[ProcessIdentity] = {
  //   var missingRefs1: List[ProcessIdentity] = StateArray.missingRefs(cpts1)
  //   val missingRefs2: List[ProcessIdentity] = StateArray.missingRefs(cpts2)
  //   // The common missing references
  //   var missingCRefs = List[ProcessIdentity]()
  //   while(missingRefs1.nonEmpty){
  //     val pid = missingRefs1.head; missingRefs1 = missingRefs1.tail
  //     if(contains(missingRefs2, pid)) missingCRefs ::= pid
  //   }
  //   missingCRefs
  // }


  // /* --------- Purging of effectOnStore.
  //  * This is done according to certain heuristics. */

  // /** The number of views when last we did a purge. */
  // private var lastPurgeViewCount = 0L

  // /** Only purge if at least purgeQuantum views have been added since the last
  //   * round of purges. */
  // private val PurgeQuantum = 300_000

  // /** Is it time for another purge? */
  // var doPurge = false

  // /** Purge from the store.  Done at the end of each ply. */
  // def purge = if(doPurge){
  //   if(ply%4 == 0) effectOnStore.purgeCandidateForMCStore(views)
  //   else if(ply%4 == 1) effectOnStore.purgeMCNotDone(views)
  //   else if(ply%4 == 2) effectOnStore.purgeMCDone(views)
  //   else if(ply%4 == 3) MissingCommon.purgeMCs()
  // }

  // /** Prepare for the next purge.  Called at the start of each ply by worker
  //   * 0. */
  // def prepareForPurge = if(ply%4 == 0){
  //   // We'll do purges only if enough views have been found since the last
  //   // round: at least PurgeQuantum and one third of the total.
  //   val viewCount = views.size; val newViewCount = viewCount-lastPurgeViewCount
  //   if(newViewCount >= PurgeQuantum && 3*newViewCount >= viewCount){
  //     println("Preparing for purge")
  //     doPurge = true; lastPurgeViewCount = viewCount
  //     effectOnStore.prepareForPurge; MissingCommon.prepareForPurge
  //   }
  //   else doPurge = false
  // }

  /* --------- Supervisory functions. */

  // def sanityCheck = effectOnStore.sanityCheck(views)

  // def report = 
  //   if(useNewEffectOnStore) newEffectOnStore.report else effectOnStore.report

  // /** Perform a memory profile of this. */
  // def memoryProfile = {
  //   import ox.gavin.profiling.MemoryProfiler.traverse
  //   if(effectOnStore != null){
  //     effectOnStore.report; println()
  //     effectOnStore.memoryProfile
  //   }
  //   if(newEffectOnStore != null) newEffectOnStore.memoryProfile
  //   traverse("effectOn", this, maxPrint = 1, ignore = List("System"))
  // }
}
