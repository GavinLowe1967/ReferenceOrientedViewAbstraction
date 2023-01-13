package ViewAbstraction

import collection.MyHashSet
import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}

/** Object to calculate the effect of the transition trans on cv with
  * singleRef.  Create extra views caused by the way the transition changes
  * cv, and add them to nextNewViews.  This version is based on
  * NewEffectOnStore. */
class NewEffectOn(
  trans: Transition, cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
    extends EffectOn(trans, cv, nextNewViews)
{
  require(singleRef && useNewEffectOnStore)

  /* Overview of main function.
   * 
   * apply
   * |--SingleRefEffectOnUnification.apply
   * |--processPrimaryInduced
   * |  |-processInducedInfo
   * |    |--EffectOn.effectOnStore.add
   * |    |--EffectOn.missingCrossRefs
   * |    |--EffectOn.commonMissingRefs
   * |    |--newEffectOnStore.add
   * |--processSecondaryInduced
   * |  |--getCrossRefs
   * |  |--processInducedInfo (as above)
   */

  import ServersReducedMap.ReducedMap 
  import Unification.UnificationList //  = List[(Int,Int)]
  import RemappingExtender.{CandidatesMap,allCompletions}
  import CompressedCandidatesMap.CompressedCandidatesMap
  import SingleRefEffectOnUnification.{
    InducedInfo, SecondaryInducedInfo, commonMissingRefs}
  //import SingleRefEffectOn.{getCrossRefs}
  import MissingCrossReferences.newMissingCrossRefs
  import NewEffectOn.{newEffectOnStore,getCrossRefs}
  import EffectOn.views

  /** The effect of the transition t on cv.  Create extra views caused by the
    * way the transition changes cv, and add them to nextNewViews. */
  override def apply() : Unit = {
    // Early bail-out if servers don't change, no chance of unification with
    // components that change state, and no chance of secondary induced
    // transitions.  
    if(trans.mightGiveSufficientUnifs(cv)){
      val (inducedInfo, secondaryInduced): (InducedInfo,SecondaryInducedInfo) =
        new SingleRefEffectOnUnification(trans,cv)()
      processPrimaryInduced(inducedInfo)
      processSecondaryInduced(secondaryInduced)
    }
  }

  /** Process the information about primary induced transitions. */
  @inline private def processPrimaryInduced(inducedInfo: InducedInfo) = {
    var index = 0
    while(index < inducedInfo.length){
      val (map, candidates, unifs, reducedMapInfo) = inducedInfo(index);
      index += 1
      Profiler.count("EffectOn step "+unifs.isEmpty)
      val cpts = mkComponents(map)
      // The components needed for condition (b).
      val crossRefs: Array[Array[State]] = 
        getCrossRefs(pre.servers, cpts, pre.components)
      if(unifs.nonEmpty || reducedMapInfo == null ||
          !cv.containsConditionBInduced(post.servers,reducedMapInfo,crossRefs)){
        val newPrinc = getNewPrinc(cpts(0), unifs)
        var newComponentsList =
          StateArray.makePostComponents(newPrinc, postCpts, cpts)
        processInducedInfo(map, unifs, reducedMapInfo, true, crossRefs,
          newComponentsList, candidates)
      }
      Pools.returnRemappingRows(map)
    } // end of while loop
  }

  /** Process the information about secondary induced transitions. */
  @inline private 
  def processSecondaryInduced(secondaryInduced: SecondaryInducedInfo) = {
    require(useNewEffectOnStore)
    var index = 0
    while(index < secondaryInduced.length){
      val (map, candidates, unifs, k) = secondaryInduced(index); index += 1
      val cpts = mkComponents(map) 
      Profiler.count("SecondaryInduced")
      val crossRefs: Array[Array[State]] = 
        getCrossRefs(pre.servers, cpts, pre.components)
      val newPrinc = getNewPrinc(cpts(0), unifs)
      val newComponentsList = List(StateArray(Array(postCpts(k), newPrinc)))
      processInducedInfo(map, unifs, null, false, crossRefs,
        newComponentsList, candidates)
      Pools.returnRemappingRows(map)
    }
  }

  /** Process information about an induced transition.  cv.components is renamed
    * by cross-reference-view-defining mapping map, to produce cpts,
    * corresponding to unifications unifs.  This will create new views
    * corresponding to each element of newComponentsList.  map can be extended
    * corresponding to candidates. */
  @inline private def processInducedInfo(
    map: RemappingMap, unifs: UnificationList,
    reducedMap: ReducedMap, isPrimary: Boolean, crossRefs: Array[Array[State]],
    newComponentsList: List[Array[State]], candidates: CompressedCandidatesMap)
      : Unit = {
    require(singleRef && useNewEffectOnStore)
    // if(candidates == null){
    //   for(t <- 0 until numTypes; id <- map(t)) assert(id >= 0)
    //   assert(!RemappingExtender.anyLinkageC(map, cv, trans.pre))
    // }
    // else assert(RemappingExtender.anyLinkageC(map, cv, trans.pre))

    // The cross reference views required for condition (b) implied by map
    val missing: Array[ReducedComponentView] = 
      MissingCrossReferences.sort(missingCrossRefs(crossRefs))
    // Is condition (c) guaranteed to be satisfied?
    val condCSat = candidates == null
    
    for(newCpts <- newComponentsList){
      val nv = Remapper.mkComponentView(post.servers, newCpts)
      if(!views.contains(nv)){
        if(missing.isEmpty){ // condition (b) satisfied  
// IMPROVE: if candidates == null then map is complete and condition (c) is 
// satisfied, so we can improve here.
          val allComps =
            RemappingExtender.allCompletions(map, candidates, cv, trans)
          // Profiler.count("NewEffectOn allCompletions "+allComps.length)
          // The average seems to be about 2, or maybe a bit less.
          for(map1 <- allComps){
            val cpts1 = Remapper.applyRemapping(map1, cv.components) 
            val inducedTrans = new InducedTransitionInfo1(
              nv.asReducedComponentView, trans, cpts1, cv)
            // New missing cross references created by extending map.  
            val newMissingCRs = newMissingCrossRefs(
              map, cv.servers, cpts1, trans.pre.components, views)
            if(newMissingCRs.nonEmpty){
              assert(!condCSat)
              // Create new MissingCrossReferences object
              val newMCR = 
                new MissingCrossReferences(inducedTrans, newMissingCRs, condCSat)
              newEffectOnStore.add(newMCR)
            }
            else{ // consider condition (c)
              val mcw = MissingCommonWrapper(inducedTrans, views)
              if(mcw == null || mcw.done){          // can fire transition
                if(nextNewViews.add(nv))
                  addedView(cpts1, newCpts, nv, unifs, isPrimary, reducedMap)
                else if(isPrimary) recordInduced(unifs, reducedMap)
                // recordInducedRedundant(
                // cpts1, newCpts, nv, unifs, isPrimary, reducedMap)
              }
              else{ assert(!condCSat); newEffectOnStore.add(mcw) }
            }
          } // end of inner for loop
        } // end of if(missing.isEmpty)
        else{
          // If candidates == null then can calculate cpts
          val cpts = 
            if(condCSat) Remapper.applyRemapping(map, cv.components) else null
          val inducedTrans = 
            InducedTransitionInfo(nv.asReducedComponentView, trans, cpts, cv)
          // Add a MissingCrossReferences to the store. 
          val missingCrossRefs =
            MissingCrossReferences(inducedTrans, missing, candidates, condCSat)
          newEffectOnStore.add(missingCrossRefs)
          if(isPrimary && unifs.isEmpty &&
              !RemappingExtender.anyLinkageC(map, cv, pre))
            cv.addConditionBInduced(post.servers, reducedMap, crossRefs)
        }
      }
      else // views already contains nv
        if(isPrimary) recordInduced(unifs, reducedMap)
        //recordInducedRedundant(cpts, newCpts, nv, unifs, isPrimary, reducedMap)
    } // end of outer for loop
  }


  /** Actions performed when a new view has been added to the view set,
    * principally setting the creation information. */
  @inline protected def addedView(
    cpts: Array[State], newComponents: Array[State], nv: ComponentView,
    unifs: UnificationList, isPrimary: Boolean, reducedMap: ReducedMap)
  = {
    Profiler.count("addedViewCount")
    if(showTransitions || ComponentView0.highlight(nv))
      showTransition(cpts, newComponents, nv, unifs, isPrimary)
    nv.setCreationInfoIndirect(trans, cpts, cv)
    if(singleRef && isPrimary) recordInduced(unifs, reducedMap)
    checkRepresentable(nv)
  }

  /** Record this induced transition if singleRef and primary, and (1) if
   ** newEffectOn, no acquired references, (2) otherwise no unifs. */
  @inline protected
  def recordInduced(unifs: UnificationList, reducedMap: ReducedMap) = {
    assert(singleRef)
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


  // ------------------------------------------------------- Helper functions

  /** Produce a new map, extending `map` to map undefined values to fresh
    * values. */
  @inline private def cloneAndExtend(map: RemappingMap): RemappingMap = {
    val map1 = Remapper.cloneMap(map)
    Remapper.mapUndefinedToFresh(map1, trans.getNextArgMap)
    map1
  }

  /** Make cpts, by applying map to cv.components.  If useNewEffectOnStore, map
    * undefined values in map to fresh values. */
  @inline private def mkComponents(map: RemappingMap): Array[State] = {
    val map1 = cloneAndExtend(map)
    val cs = Remapper.applyRemapping(map1, cv.components)
    Pools.returnRemappingRows(map1); cs
  }

  /** All cross references implied by map.  These can only be via references
    * where map is defined. */
  @inline private def makeCrossRefs(map: RemappingMap): Array[Array[State]] = {
    val cpts = mkComponents(map)
    getCrossRefs(pre.servers, cpts, pre.components)
  }

  /** The missing cross reference views required for condition (b). */
  @inline protected def missingCrossRefs(crossRefs: Array[Array[State]])
      : Array[ReducedComponentView] =
    crossRefs.map{ cpts => ReducedComponentView(pre.servers, cpts) }.
      filter(!views.contains(_))
}

// =======================================================

object NewEffectOn{
  @inline private def guard = singleRef && useNewEffectOnStore

  private var newEffectOnStore: NewEffectOnStore =
    if(guard) new NewEffectOnStore else null

  def reset = {
    if(guard) newEffectOnStore = new NewEffectOnStore
    lastPurgeViewCount = 0L; doPurge = false
  }

  import EffectOn.{views}

  /** If cv completes a delayed transition in effectOnStore, then complete it. */
  def completeDelayed(cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
  = {
    require(guard)
    val newViews = newEffectOnStore.complete(cv, views)
    for(nv <- newViews){
      if(showTransitions || ComponentView0.highlight(nv)) 
        println(s"Adding $nv\n from completeDelayed($cv)")
      tryAddView(nv, nextNewViews)
    }
  }

  /** Add mi.nextNewViews to nextNewViews.  */
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
        val (trans, _, cv, _) = nv.getCreationIngredients
        println("Not enough identities in script to combine transition\n"+
          s"$trans and\n$cv.  Produced view\n"+nv.toString0)
        sys.exit()
      }
    } // end of outer if
  }

  /** Get (the components of) the cross reference views between cpts1 and cpts2,
    * needed for condition (b). 
    * 
    * The result is sorted according to StateArray.lessThan.  Each element is
    * the value registered in StateArray. */
  @inline def getCrossRefs(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
      : Array[Array[State]] = {
    assert(singleRef)
    val cr0 = StateArray.crossRefs(cpts1, cpts2)
    val cr1 = cr0.map(Remapper.remapComponents(servers,_)).distinct
    // IMPROVE: remove duplicates in sortCrossRefs
    StateArray.sortCrossRefs(cr1)
    cr1
  }

  /* ============================================ Purging of effectOnStore.
   * This is done according to certain heuristics. */

  /** The number of views when last we did a purge. */
  private var lastPurgeViewCount = 0L

  /** Only purge if at least purgeQuantum views have been added since the last
    * round of purges. */
  private val PurgeQuantum = 300_000

  /** Is it time for another purge? */
  var doPurge = false

  /** Test if it's time for a purge.  */
  def testPurge: Boolean = 
    if(ply%4 == 0){
      // We'll do purges only if enough views have been found since the last
      // round: at least PurgeQuantum and one third of the total.
      val viewCount = views.size; val newViewCount = viewCount-lastPurgeViewCount
      if(newViewCount >= PurgeQuantum && 3*newViewCount >= viewCount){
        println("Preparing for purge")
        lastPurgeViewCount = viewCount; true
      }
      else false
    }
    else false

  /** If it's time for the next purge, then set doPurge and prepare for it.
    * Called at the start of each ply by worker 0. */
  def prepareForPurge = if(ply%4 == 0){
    doPurge = testPurge
    if(doPurge){  
      newEffectOnStore.prepareForPurge; MissingCommon.prepareForPurge
    }
  }

  /** Purge from the store.  Done at the end of each ply. */
  def purge = {
    // Profiler.count(s"purge $ply $doPurge")
    if(doPurge){
      if(ply%4 == 0) newEffectOnStore.purgeByNewView(views) 
      else if(ply%4 == 1) newEffectOnStore.purgeMissingCrossRefStore(views)
      // Note: purgeMissingCrossRefStore builds on purgeByNewView
      else if(ply%4 == 2){
        newEffectOnStore.purgeMissingCommonStore(views)
        newEffectOnStore.purgeCandidateForMCStore(views)
      }
      else if(ply%4 == 3) MissingCommon.purgeMCs()
    }
  }

  // ============================================ Administrative functions

  def report = { require(guard); newEffectOnStore.report }

  def sanityCheck = newEffectOnStore.sanityCheck _

  /** Perform a memory profile of this. */
  def memoryProfile = {
    require(guard)
    import ox.gavin.profiling.MemoryProfiler.traverse
    newEffectOnStore.memoryProfile
    traverse("NewEffectOn", this, maxPrint = 1, ignore = List("System"))
  }
}
