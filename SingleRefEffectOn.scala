package ViewAbstraction

import collection.MyHashSet
import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}

/** Object to calculate the effect of the transition trans on cv with
  * singleRef.  Create extra views caused by the way the transition changes
  * cv, and add them to nextNewViews. */
class SingleRefEffectOn(
  trans: Transition, cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
    extends EffectOn(trans, cv, nextNewViews)
{
  require(singleRef)

  import ServersReducedMap.ReducedMap 
  import Unification.UnificationList //  = List[(Int,Int)]
  import RemappingExtender.Linkage
  import SingleRefEffectOnUnification.{InducedInfo, SecondaryInducedInfo}
  import SingleRefEffectOn.{getCrossRefs,commonMissingRefs,effectOnStore,newEffectOnStore}
  import EffectOn.views

  //private var sreou: SingleRefEffectOnUnification = null

  /** The effect of the transition t on cv.  Create extra views caused by the
    * way the transition changes cv, and add them to nextNewViews. */
  override def apply() : Unit = {
    // Early bail-out if servers don't change, no chance of unification with
    // components that change state, and no chance of secondary induced
    // transitions.  This captures over about 25% of cases with lazySet.csp,
    // bound 44; nearly all other cases have servers that change state.
    if(trans.mightGiveSufficientUnifs(cv)){
      // inducedInfo: ArrayBuffer[(RemappingMap, Array[State], UnificationList,
      // ReducedMap)] is a set of tuples (pi, pi(cv.cpts), unifs, reducedMap)
      // where pi is a unification function corresponding to
      // unifs. secondaryInducedArray: Buffer[(Array[State], UnificationList,
      // Int) is similar for secondary induced transitions, where the final
      // component is the index of preCpts/postCpts that gains a reference to
      // cv.principal.
      sreou = new SingleRefEffectOnUnification(trans,cv)
      val (inducedInfo, secondaryInduced): (InducedInfo,SecondaryInducedInfo) =
        sreou()
      processInduced(inducedInfo);
      processSecondaryInduced(secondaryInduced)
    }
  }

  /** Process the information about primary induced transitions. */
  @inline private def processInduced(inducedInfo: InducedInfo) = {
    assert(singleRef)
    var index = 0
    while(index < inducedInfo.length){
      val (map, rrParams, linkages, unifs, reducedMapInfo) = inducedInfo(index);
      index += 1
      Profiler.count("EffectOn step "+unifs.isEmpty)
      val cpts = mkComponents(map)
      // The components needed for condition (b).
      val crossRefs: List[Array[State]] =
        getCrossRefs(pre.servers, cpts, pre.components)
      if(unifs.nonEmpty || reducedMapInfo == null ||
          !cv.containsConditionBInduced(post.servers,reducedMapInfo,crossRefs)){
        val newPrinc = getNewPrinc(cpts(0), unifs)
        // If singleRef, the principals are unified, but the principal loses
        // the reference to the second component, we can ignore this case.  
        // Actually, I'm not sure about this.
        // if(singleRef && unifs.contains((0,0)) && cpts.length == 2 &&
        //   !newPrinc.hasIncludedParam(cpts(1).componentProcessIdentity)){ }
        // else{
        var newComponentsList =
          StateArray.makePostComponents(newPrinc, postCpts, cpts)
        processInducedInfo(map, cpts, unifs, reducedMapInfo, true, crossRefs, 
          newComponentsList, rrParams, linkages)
      }
      Pools.returnRemappingRows(map)
    } // end of while loop
  }



  /** Process the information about secondary induced transitions. */
  @inline private
  def processSecondaryInduced(secondaryInduced: SecondaryInducedInfo)  = {
    var index = 0
    while(index < secondaryInduced.length){
      val (map, rrParams, linkages, unifs, k) = secondaryInduced(index); 
      index += 1
      val cpts = mkComponents(map) 
      Profiler.count("SecondaryInduced")
      val crossRefs: List[Array[State]] =
        getCrossRefs(pre.servers, cpts, pre.components)
      val newPrinc = getNewPrinc(cpts(0), unifs)
      val newComponentsList = List(StateArray(Array(postCpts(k), newPrinc)))
      processInducedInfo(map, cpts, unifs, null, false, crossRefs, 
        newComponentsList, rrParams, linkages)
    }
  }

  /** Create induced transition producing views with post.servers and each
    * element of newComponentsList.  The transition is induced by pre -e->
    * post acting on cv, with unifications unifs; cv.cpts is remapped
    * to produce cpts.  Add result to nextNewViews.
    * 
    * This function would live better inside apply; but that function is too
    * large.  Most other parameters are as there (most are used only for
    * setting creation information or textual output).
    * @param isPrimary are we creating a primary transition?
    * @param reducedMap a representation of the RemappingMap |> post.servers. */
  @inline private 
  def processInducedInfo(map: RemappingMap, cpts: Array[State], 
    unifs: UnificationList, reducedMap: ReducedMap, isPrimary: Boolean, 
    crossRefs: List[Array[State]], newComponentsList: List[Array[State]],
    rrParams: BitMap, linkages: List[Linkage])
      : Unit = {
    assert(singleRef)
    Profiler.count(s"processInducedInfo $isPrimary")
    // assert(cpts.map(_.cs).sameElements(cv.components.map(_.cs)))
    //for(cpts <- newComponentsList) ComponentView0.checkValid(pre.servers, cpts)
    // StateArray.checkDistinct(cpts); assert(cpts.length==cv.components.length)
    // assert(!pre.components.sameElements(cpts),
    //   s"pre = $pre; cpts = "+StateArray.show(cpts))

    // Dispatch appropriate version
    if(useNewEffectOnStore){
      // All completions of map
      val allCompletions = sreou.allCompletions(rrParams, map, linkages)
      for(map1 <- allCompletions)
        processInducedInfoNewEffectOnStore(
          map1, cpts, unifs, reducedMap, isPrimary, crossRefs, newComponentsList)
    }
    else processInducedInfoSingleRef(
      cpts, unifs, reducedMap, isPrimary, crossRefs, newComponentsList)
// IMPROVE: recycle map
  }



  /** Process induced information in the case of singleRef. */
  @inline private def processInducedInfoSingleRef(
    cpts: Array[State], unifs: UnificationList, reducedMap: ReducedMap,
    isPrimary: Boolean, crossRefs: List[Array[State]],
    newComponentsList: List[Array[State]])
      : Unit = {
    require(singleRef)
    val missingCommons: List[MissingCommon] =
      checkCompatibleMissing(pre.servers, pre.components, cpts)
    // If there are references between components from pre and cv, then check
    // that that combination is possible in sysAbsViews: those that are
    // missing.
    val missing: List[ReducedComponentView] = missingCrossRefs(crossRefs)
    for(newComponents <- newComponentsList){
      val nv = Remapper.mkComponentView(post.servers, newComponents)
      Profiler.count("newViewCount") 
      if(!views.contains(nv)){
        if(missing.isEmpty && missingCommons.isEmpty){
          if(nextNewViews.add(nv))
            addedView/*RecordInduced*/(cpts, newComponents, nv, unifs, isPrimary, reducedMap)
          else recordInducedRedundant(
            cpts, newComponents, nv, unifs, isPrimary, reducedMap)
        }
        else{ // missing.nonEmpty || missingCommons.nonEmpty 
          effectOnStore.add(missing, missingCommons, nv, trans,
            cpts, cv, newComponents)
          // Note: the missingCommons may be shared.
          nv.setCreationInfoIndirect(trans, cpts, cv, newComponents)
          // IMPROVE: do we need to check isPrimary here?
          if(isPrimary && unifs.isEmpty && missingCommons.isEmpty){
            cv.addConditionBInduced(post.servers, reducedMap, crossRefs)
          }
        }
      } // end of if(!views.contains(nv))
      // Try to work out why so many cases are redundant
      else // views already contains nv
        recordInducedRedundant(
          cpts, newComponents, nv, unifs, isPrimary, reducedMap)
    } // end of for loop
  } // end of processInducedInfo

  /** Process induced information in the case of singleRef and using the
    * NewEffectOnStore. */
  @inline protected 
  def processInducedInfoNewEffectOnStore(
    map: RemappingMap, cpts: Array[State], unifs: UnificationList,
    reducedMap: ReducedMap, isPrimary: Boolean, crossRefs: List[Array[State]],
    newComponentsList: List[Array[State]])
      : Unit = {
    require(singleRef && useNewEffectOnStore)
    // The cross reference views required for condition (b)
    val missing: Array[ReducedComponentView] = 
      MissingCrossReferences.sort(missingCrossRefs(crossRefs).toArray)
    // The common missing references for condition (c)
    val commonMissingPids =  commonMissingRefs(pre.components, cpts).toArray
    
    for(newCpts <- newComponentsList){
      val nv = Remapper.mkComponentView(post.servers, newCpts)
      if(!views.contains(nv)){
        val inducedTrans = new InducedTransitionInfo(nv.asReducedComponentView, 
          trans, cpts, cv, newCpts)

        if(missing.isEmpty){
          val mcw = MissingCommonWrapper(inducedTrans, commonMissingPids, views)
          if(mcw == null){          // can fire transition
            if(nextNewViews.add(nv))
              addedView/*RecordInduced*/(cpts, newCpts, nv, unifs, isPrimary, reducedMap)
            else recordInducedRedundant(
              cpts, newCpts, nv, unifs, isPrimary, reducedMap)
          }
          else{
            newEffectOnStore.add(mcw)
          }
        } // end of if(missing.isEmpty)
        else{
          // Add a MissingCrossReferences to the store
          newEffectOnStore.add(inducedTrans, missing, map, commonMissingPids)
          if(isPrimary && unifs.isEmpty && commonMissingPids.isEmpty){
// IMPROVE make the MissingCommon and test if empty ??
            cv.addConditionBInduced(post.servers, reducedMap, crossRefs)
          }
        }
      }
      else // views already contains nv
        recordInducedRedundant(cpts, newCpts, nv, unifs, isPrimary, reducedMap)
    } // end of for loop
  }
/*
  /** Record this induced transition if singleRef and primary, and (1) if
   ** newEffectOn, no acquired references, (2) otherwise no unifs. */
  @inline private 
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
 */

/*
  def addedViewRecordInduced(
    cpts: Array[State], newComponents: Array[State], nv: ComponentView,
    unifs: UnificationList, isPrimary: Boolean, reducedMap: ReducedMap)
  = {
    addedView(cpts, newComponents, nv, unifs, isPrimary, reducedMap)
    recordInduced(unifs, reducedMap)
  }
 */

  /** Record the induced transition, and show it was redundant. */
  @inline private def recordInducedRedundant(
    cpts: Array[State], newComponents: Array[State], nv: ComponentView,
    unifs: UnificationList, isPrimary: Boolean, reducedMap: ReducedMap)
  = {
    assert(singleRef)
    if(isPrimary) recordInduced(unifs, reducedMap)
    showRedundancy(views.get(nv), cpts, newComponents, nv, unifs, isPrimary)
  }

  /** The missing cross reference views required for condition (b). */
  @inline private def missingCrossRefs(crossRefs: List[Array[State]])
      : List[ReducedComponentView] =
    crossRefs.map{ cpts => ReducedComponentView(pre.servers, cpts) }.
      filter(!views.contains(_))


  /** Test whether, if the principal components of cpts1 and cpts2 both have a
    * reference to the same missing component then there is a way of
    * instantiating that component, consistent with the current set of views.
    * Here cpts1 corresponds to the pre-state of a transition, and cpts2 to
    * the view acted upon.
    * 
    * Pre: servers || cpts1 is in normal form.
    * @return the identities of all such missing components. */ 
  private def checkCompatibleMissing(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
      : List[MissingCommon]  = {
    require(singleRef)
    // The common missing references
    var missingCRefs: List[ProcessIdentity] = commonMissingRefs(cpts1, cpts2)
    // Representation of the common missing references considered so far for
    // which there is no way of instantiating the referenced component.
    var missingCommons = List[MissingCommon]()
    while(missingCRefs.nonEmpty){
      val pid = missingCRefs.head; missingCRefs = missingCRefs.tail
      val mc = MissingCommon.makeMissingCommon(servers, cpts1, cpts2, pid, views)
      if(mc != null){
// FIXME: if the component c has a reference to one of the present secondary
// components, or vice versa, check that that combination is also possible.
// (Later:) isn't this just missingCrossRefs?
        if(verbose){
          println(s"checkCompatibleMissing($servers, ${StateArray.show(cpts1)},"+
            s" ${StateArray.show(cpts2)})")
          println(s"Failed to find states to instantiate common reference $pid")
        }
        missingCommons ::= mc
      }
    } // end of iteration over missingCRefs
    missingCommons
  }

}


// =======================================================

object SingleRefEffectOn{

  /** A mapping showing which component views might be added later.
    * Abstractly it stores tuples (missing, missingCommon, nv) such that:
    * missing is a set of views; missingCommon is a set of (ServerStates, State,
    * State, ProcessIdentity) tuples; and nv is a view.  If
    * 
    * (1) all the views in missing are added; and
    * 
    * (2) views are added so all elements of missingCommon satisfy
    * hasCommonRef; i.e. for each (servers, princ1, princ2, pid) in
    * missingCommon, there is a component state c with identity pid such that
    * servers || princ1 || c and servers || princ2 || c are both in sysAbsViews
    * (up to renaming);
    * 
    * then nv can also be added.
    * 
    * Tuples are added to the store in apply when a transition is prevented
    * because relevant views are not yet in the store.  completeDelayed
    * subsequently tries to complete the transitions.  */
  var effectOnStore: EffectOnStore = 
    if(singleRef && !useNewEffectOnStore) new SimpleEffectOnStore else null

  var newEffectOnStore: NewEffectOnStore =
    if(singleRef && useNewEffectOnStore) new NewEffectOnStore else null


  def reset = { 
    if(singleRef){
      if(useNewEffectOnStore) newEffectOnStore = new NewEffectOnStore
      else effectOnStore = new SimpleEffectOnStore
    }
    lastPurgeViewCount = 0L; doPurge = false
  }



  import EffectOn.{views}

  /* --------- Purging of effectOnStore.
   * This is done according to certain heuristics. */

  /** The number of views when last we did a purge. */
  private var lastPurgeViewCount = 0L

  /** Only purge if at least purgeQuantum views have been added since the last
    * round of purges. */
  private val PurgeQuantum = 300_000

  /** Is it time for another purge? */
  var doPurge = false

  /** Purge from the store.  Done at the end of each ply. */
  def purge = if(doPurge){
    if(ply%4 == 0) effectOnStore.purgeCandidateForMCStore(views)
    else if(ply%4 == 1) effectOnStore.purgeMCNotDone(views)
    else if(ply%4 == 2) effectOnStore.purgeMCDone(views)
    else if(ply%4 == 3) MissingCommon.purgeMCs()
  }

  /** Prepare for the next purge.  Called at the start of each ply by worker
    * 0. */
  def prepareForPurge = if(ply%4 == 0){
    // We'll do purges only if enough views have been found since the last
    // round: at least PurgeQuantum and one third of the total.
    val viewCount = views.size; val newViewCount = viewCount-lastPurgeViewCount
    if(newViewCount >= PurgeQuantum && 3*newViewCount >= viewCount){
      println("Preparing for purge")
      doPurge = true; lastPurgeViewCount = viewCount
      effectOnStore.prepareForPurge; MissingCommon.prepareForPurge
    }
    else doPurge = false
  }

  /** If cv completes a delayed transition in effectOnStore, then complete it. */
  def completeDelayed(cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
  = {
    val newViews =
      if(useNewEffectOnStore) newEffectOnStore.complete(cv, views)
      else effectOnStore.complete(cv, views)
    // if(highlight(cv)) println(s"completeDelayed($cv)")
    for(nv <- newViews){
      if(showTransitions || ComponentView0.highlight(nv)) 
        println(s"Adding $nv\n from completeDelayed($cv)")
      tryAddView(nv, nextNewViews)
    }
  }

  /** Add mi.nextNewViews to nextNewViews. */
  @inline private 
  def tryAddView(nv: ComponentView, nextNewViews: MyHashSet[ComponentView]) = {
    // require(mi.done); val nv = mi.newView
    if(nextNewViews.add(nv)){
      if(showTransitions || ComponentView0.highlight(nv)){
        val (trans, cpts, cv, newComponents) = nv.getCreationIngredients
        println(s"Adding via completeDelayed \n"+
          s"$trans induces \n"+
          EffectOnStore.showInduced(
            cv, cpts, trans.post.servers, newComponents, nv))
      }
      if(!nv.representableInScript){
        val (trans, cpts, cv, newComponents) = nv.getCreationIngredients
        println("Not enough identities in script to combine transition\n"+
          s"$trans and\n$cv.  Produced view\n"+nv.toString0)
        sys.exit()
      }
    } // end of outer if
  }

  /** Get (the components of) the cross reference views between cpts1 and cpts2,
    * needed for condition (b). */
  @inline def getCrossRefs(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
      : List[Array[State]] = {
    assert(singleRef)
    StateArray.crossRefs(cpts1, cpts2).map(Remapper.remapComponents(servers,_))
  }

  /** Get (the components of) the cross reference views between map(cpts1) and
    * cpts2, needed for condition (b).  map might be undefined on some
    * components of cpts1: only consider those states of cpts1 where the map
    * is fully defined. */
  @inline private def getCrossRefs1(servers: ServerStates, 
    cpts1: Array[State], cpts2: Array[State], map: RemappingMap)
      : List[Array[State]] = {
    val cpts1Renamed = 
      cpts1.filter(Remapper.isDefinedOver(map, _)).
        map(Remapper.applyRemappingToState(map,_))
    getCrossRefs(servers, cpts1Renamed, cpts2)
  }

  /** All common included missing references from cpts1 and cpts2. */
  @inline def commonMissingRefs(cpts1: Array[State], cpts2: Array[State])
      : List[ProcessIdentity] = {
    var missingRefs1: List[ProcessIdentity] = StateArray.missingRefs(cpts1)
    val missingRefs2: List[ProcessIdentity] = StateArray.missingRefs(cpts2)
    // The common missing references
    var missingCRefs = List[ProcessIdentity]()
    while(missingRefs1.nonEmpty){
      val pid = missingRefs1.head; missingRefs1 = missingRefs1.tail
      if(contains(missingRefs2, pid)) missingCRefs ::= pid
    }
    missingCRefs
  }

  /* --------- Supervisory functions. */

  def sanityCheck = effectOnStore.sanityCheck(views)

  def report = 
    if(useNewEffectOnStore) newEffectOnStore.report else effectOnStore.report

  /** Perform a memory profile of this. */
  def memoryProfile = {
    import ox.gavin.profiling.MemoryProfiler.traverse
    if(effectOnStore != null){
      effectOnStore.report; println()
      effectOnStore.memoryProfile
    }
    if(newEffectOnStore != null) newEffectOnStore.memoryProfile
    traverse("SingleRefEffectOn", this, maxPrint = 1, ignore = List("System"))
  }
}
