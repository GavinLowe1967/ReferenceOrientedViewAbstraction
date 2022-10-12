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
  import RemappingExtender.{CandidatesMap}
  import SingleRefEffectOnUnification.{InducedInfo, SecondaryInducedInfo, commonMissingRefs}
  import SingleRefEffectOn.{getCrossRefs}
  import NewEffectOn.{newEffectOnStore}
  import EffectOn.views

  /** The effect of the transition t on cv.  Create extra views caused by the
    * way the transition changes cv, and add them to nextNewViews. */
  override def apply() : Unit = {
    // Early bail-out if servers don't change, no chance of unification with
    // components that change state, and no chance of secondary induced
    // transitions.  
    if(trans.mightGiveSufficientUnifs(cv)){
      //val sreou = new SingleRefEffectOnUnification(trans,cv)
      val (inducedInfo, secondaryInduced): (InducedInfo,SecondaryInducedInfo) =
        new SingleRefEffectOnUnification(trans,cv)()
      processPrimaryInduced(inducedInfo)
      processSecondaryInduced(secondaryInduced)
    }
  }


  /** Process the information about primary induced transitions. */
  @inline private 
  def processPrimaryInduced(inducedInfo: InducedInfo) = {
    var index = 0
    while(index < inducedInfo.length){
      val (map, candidates, unifs, reducedMapInfo) = inducedInfo(index);
      index += 1
//       val allCompletions = 
//         if(true) List(mapX) else sreou.allCompletions(mapX, candidates)
// for(map <- allCompletions){
      Profiler.count("EffectOn step "+unifs.isEmpty)
      val cpts = mkComponents(map)
      // The components needed for condition (b).
      val crossRefs: List[Array[State]] = //makeCrossRefs(map)
        getCrossRefs(pre.servers, cpts, pre.components)
      if(unifs.nonEmpty || reducedMapInfo == null ||
          !cv.containsConditionBInduced(post.servers,reducedMapInfo,crossRefs)){
        val newPrinc = getNewPrinc(cpts(0), unifs)
        var newComponentsList =
          StateArray.makePostComponents(newPrinc, postCpts, cpts)
        processInducedInfo(map, cpts, unifs, reducedMapInfo, true, crossRefs,
          newComponentsList, candidates)
      }
      Pools.returnRemappingRows(map)
//}
    } // end of while loop
  }

  /** Process the information about secondary induced transitions. */
  @inline private 
  def processSecondaryInduced(secondaryInduced: SecondaryInducedInfo) = {
    require(useNewEffectOnStore)
    var index = 0
    while(index < secondaryInduced.length){
      val (map, candidates, unifs, k) = secondaryInduced(index); index += 1
//       val allCompletions = 
//         if(true) List(mapX) else sreou.allCompletions(mapX, candidates)
// for(map <- allCompletions){
      val cpts = mkComponents(map) 
      Profiler.count("SecondaryInduced")
      val crossRefs: List[Array[State]] =
        getCrossRefs(pre.servers, cpts, pre.components)
      val newPrinc = getNewPrinc(cpts(0), unifs)
      val newComponentsList = List(StateArray(Array(postCpts(k), newPrinc)))
      processInducedInfo(map, cpts, unifs, null, false, crossRefs,
        newComponentsList, candidates)
//}
    }
  }

 def processInducedInfo(
    map: RemappingMap, cpts: Array[State], unifs: UnificationList,
    reducedMap: ReducedMap, isPrimary: Boolean, crossRefs: List[Array[State]],
    newComponentsList: List[Array[State]], candidates: CandidatesMap) 
     : Unit =
   if(lazyNewEffectOnStore) 
     processInducedInfoLazy(map, cpts, unifs, reducedMap, isPrimary, crossRefs,
       newComponentsList, candidates)
   else 
     processInducedInfoOld(map, cpts, unifs, reducedMap, isPrimary, crossRefs,
       newComponentsList, candidates)

  /** Process induced information. */
// IMPROVE comment
  @inline protected 
  def processInducedInfoOld(
    map: RemappingMap, cpts: Array[State], unifs: UnificationList,
    reducedMap: ReducedMap, isPrimary: Boolean, crossRefs: List[Array[State]],
    newComponentsList: List[Array[State]], candidates: CandidatesMap)
      : Unit = {
// NOTE: several of the parameters are unused
    require(singleRef && useNewEffectOnStore && !lazyNewEffectOnStore)
    // The cross reference views required for condition (b)
    // val missing: Array[ReducedComponentView] = 
    //   MissingCrossReferences.sort(missingCrossRefs(crossRefs).toArray)
    
    for(newCpts <- newComponentsList){
      val nv = Remapper.mkComponentView(post.servers, newCpts)
      if(!views.contains(nv)){
        val allCompletions =
          RemappingExtender.allCompletions(map, candidates,trans)
        for(map1 <- allCompletions){
          val cpts1 =  Remapper.applyRemapping(map1, cv.components)
          val crossRefs1 = getCrossRefs(pre.servers, cpts1, pre.components)
          // assert(crossRefs.length == crossRefs1.length)
          // for(i <- 0 until crossRefs.length)
          //   assert(crossRefs(i).sameElements(crossRefs1(i)))
          val missing1: Array[ReducedComponentView] =
            MissingCrossReferences.sort(missingCrossRefs(crossRefs1).toArray)
          val inducedTrans = new InducedTransitionInfo(nv.asReducedComponentView,
            trans, cpts1, cv, newCpts)
          // The common missing references for condition (c)
          val commonMissingPids = 
            if(lazyNewEffectOnStore) null 
            else commonMissingRefs(pre.components, cpts1).toArray
          if(missing1.isEmpty){ // condition (b) satisfied
            val mcw =
              MissingCommonWrapper(inducedTrans, commonMissingPids, views)
            if(mcw == null){          // can fire transition
              if(nextNewViews.add(nv))
                addedView(cpts1, newCpts, nv, unifs, isPrimary, reducedMap)
              else recordInducedRedundant(
                cpts1, newCpts, nv, unifs, isPrimary, reducedMap)
            }
            else newEffectOnStore.add(mcw)
          } // end of if(missing.isEmpty)
          else{
            // Add a MissingCrossReferences to the store
            val missingCrossRefs = new MissingCrossReferences(
              inducedTrans, missing1, map1, candidates, commonMissingPids)
            newEffectOnStore.add(missingCrossRefs)
            if(isPrimary && unifs.isEmpty && commonMissingPids.isEmpty)
              cv.addConditionBInduced(post.servers, reducedMap, crossRefs1)
          }
        } // end of inner for loop
      }
      else // views already contains nv
        recordInducedRedundant(cpts, newCpts, nv, unifs, isPrimary, reducedMap)
    } // end of for loop
  }


  @inline protected 
  def processInducedInfoLazy(
    map: RemappingMap, cpts: Array[State], unifs: UnificationList,
    reducedMap: ReducedMap, isPrimary: Boolean, crossRefs: List[Array[State]],
    newComponentsList: List[Array[State]], candidates: CandidatesMap)
      : Unit = {
// IMPROVE: several params not used
    require(singleRef && useNewEffectOnStore && lazyNewEffectOnStore)
    // The cross reference views required for condition (b) implied by map
    val missing: Array[ReducedComponentView] = 
      MissingCrossReferences.sort(missingCrossRefs(crossRefs).toArray)
    
    for(newCpts <- newComponentsList){
      val nv = Remapper.mkComponentView(post.servers, newCpts)
      if(!views.contains(nv)){
        if(missing.isEmpty){ // condition (b) satisfied            
          for(map1 <- RemappingExtender.allCompletions(map, candidates,trans)){
// FIXME: we also need to know if any of the completions creates a new cross
// reference.
            val cpts1 = mkComponents(map1)
            val inducedTrans = new InducedTransitionInfo(
              nv.asReducedComponentView, trans, cpts1, cv, newCpts)
            val mcw = MissingCommonWrapper.fromMap(map1, inducedTrans, views)
            if(mcw == null){          // can fire transition
              if(nextNewViews.add(nv))
                addedView(cpts1, newCpts, nv, unifs, isPrimary, reducedMap)
              else recordInducedRedundant(
                cpts1, newCpts, nv, unifs, isPrimary, reducedMap)
            }
            else newEffectOnStore.add(mcw)
          } // end of inner for loop
        } // end of if(missing.isEmpty)
        else{
          val inducedTrans = new InducedTransitionInfo(nv.asReducedComponentView,
            trans, null, cv, newCpts)
          // Add a MissingCrossReferences to the store.  Note: map is cloned to
          // prevent sharing, as it's sometimes mutated.
          val missingCrossRefs = new MissingCrossReferences(
            inducedTrans, missing, Remapper.cloneMap(map), candidates, null)
          newEffectOnStore.add(missingCrossRefs)
          if(isPrimary && unifs.isEmpty && false){
// IMPROVE
            cv.addConditionBInduced(post.servers, reducedMap, crossRefs)
          }
        }
      }
      else // views already contains nv
        recordInducedRedundant(cpts, newCpts, nv, unifs, isPrimary, reducedMap)
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
  @inline private def makeCrossRefs(map: RemappingMap): List[Array[State]] = {
    val cpts = mkComponents(map)
    getCrossRefs(pre.servers, cpts, pre.components)
  }


}

// =======================================================

object NewEffectOn{
  @inline private def guard = singleRef && useNewEffectOnStore

  var newEffectOnStore: NewEffectOnStore =
    if(guard) new NewEffectOnStore else null

  def reset =  if(guard) newEffectOnStore = new NewEffectOnStore

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

  def report = { require(guard); newEffectOnStore.report }

  /** Perform a memory profile of this. */
  def memoryProfile = {
    require(guard)
    import ox.gavin.profiling.MemoryProfiler.traverse
    newEffectOnStore.memoryProfile
    traverse("NewEffectOn", this, maxPrint = 1, ignore = List("System"))
  }
}
