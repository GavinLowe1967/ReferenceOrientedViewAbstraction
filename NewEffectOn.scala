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
    extends SingleRefEffectOn(trans, cv, nextNewViews)
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
  import SingleRefEffectOn.{getCrossRefs}
  import InducedTransitionInfo.newMissingCrossRefs
  import NewEffectOn.{newEffectOnStore}
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
// IMPROVE
if(true){
    if(candidates == null){
      for(t <- 0 until numTypes; id <- map(t)) assert(id >= 0)
      assert(!RemappingExtender.anyLinkageC(map, cv, trans.pre))
    }
    else assert(RemappingExtender.anyLinkageC(map, cv, trans.pre))
}
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
              nv.asReducedComponentView, trans, cpts1, cv) // , newCpts)
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
              //if(/*true ||*/ mcw != null){
                if(mcw == null || mcw.done){          // can fire transition
                  if(nextNewViews.add(nv))
                    addedView(cpts1, newCpts, nv, unifs, isPrimary, reducedMap)
                  else if(isPrimary) recordInduced(unifs, reducedMap)
                  // recordInducedRedundant(
                  // cpts1, newCpts, nv, unifs, isPrimary, reducedMap)
                }
                else{ assert(!condCSat); newEffectOnStore.add(mcw) }
              //} // if mcr == null, subsumed
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
}

// =======================================================

object NewEffectOn{
  @inline private def guard = singleRef && useNewEffectOnStore

  private var newEffectOnStore: NewEffectOnStore =
    if(guard) new NewEffectOnStore else null

  def reset = if(guard) newEffectOnStore = new NewEffectOnStore

  import EffectOn.{views}

  /** If cv completes a delayed transition in effectOnStore, then complete it. */
  def completeDelayed(cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
  = {
    require(guard)
    val newViews = newEffectOnStore.complete(cv, views)
    for(nv <- newViews){
      if(showTransitions || ComponentView0.highlight(nv)) 
        println(s"Adding $nv\n from completeDelayed($cv)")
      SingleRefEffectOn.tryAddView(nv, nextNewViews)
    }
  }

  /** Is it time for another purge? */
  private var doPurge = false

  /** If it's time for the next purge, then set doPurge and prepare for it.
    * Called at the start of each ply by worker 0. */
  def prepareForPurge = if(ply%4 == 0){
    doPurge = SingleRefEffectOn.testPurge
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
