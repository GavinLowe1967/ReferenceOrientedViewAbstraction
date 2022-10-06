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

  import ServersReducedMap.ReducedMap 
  import Unification.UnificationList //  = List[(Int,Int)]
  import RemappingExtender.Linkage
  import SingleRefEffectOnUnification.{InducedInfo, SecondaryInducedInfo}
  import SingleRefEffectOn.{getCrossRefs, commonMissingRefs} //, effectOnStore,
  import NewEffectOn.{newEffectOnStore}
  import EffectOn.views

  //private var sreou: SingleRefEffectOnUnification = null

  /** The effect of the transition t on cv.  Create extra views caused by the
    * way the transition changes cv, and add them to nextNewViews. */
  override def apply() : Unit = {
    // Early bail-out if servers don't change, no chance of unification with
    // components that change state, and no chance of secondary induced
    // transitions.  
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
      processPrimaryInducedNewEffectOnStore(inducedInfo)
      processSecondaryInducedNewEffectOnStore(secondaryInduced)
    }
  }


  /** Make cpts, by applying map to cv.components.  If useNewEffectOnStore, map
    * undefined values in map to fresh values. */
  @inline protected def mkComponents(map: RemappingMap): Array[State] = {
    val map1 = Remapper.cloneMap(map)
    Remapper.mapUndefinedToFresh(map1, trans.getNextArgMap)
    val cs = Remapper.applyRemapping(map1, cv.components)
    Pools.returnRemappingRows(map1); cs
  }

  /** Process the information about primary induced transitions. */
  @inline private 
  def processPrimaryInducedNewEffectOnStore(inducedInfo: InducedInfo) = {
    assert(singleRef && useNewEffectOnStore)
    var index = 0
    while(index < inducedInfo.length){
      val (mapX, rrParams, linkages, unifs, reducedMapInfo) = inducedInfo(index);
      index += 1
//FIXME
      val allCompletions = 
        if(false) List(mapX) else sreou.allCompletions(rrParams, mapX, linkages)
for(map <- allCompletions){
      Profiler.count("EffectOn step "+unifs.isEmpty)
      val cpts = mkComponents(map)
      // The components needed for condition (b).
      val crossRefs: List[Array[State]] =
        getCrossRefs(pre.servers, cpts, pre.components)
      if(unifs.nonEmpty || reducedMapInfo == null ||
          !cv.containsConditionBInduced(post.servers,reducedMapInfo,crossRefs)){
        val newPrinc = getNewPrinc(cpts(0), unifs)
        var newComponentsList =
          StateArray.makePostComponents(newPrinc, postCpts, cpts)
        processInducedInfoNewEffectOnStore(
          map, cpts, unifs, reducedMapInfo, true, crossRefs,
          newComponentsList) // , rrParams, linkages)
        // processInducedInfo(map, cpts, unifs, reducedMapInfo, true, crossRefs, 
        //   newComponentsList, rrParams, linkages)
      }
      Pools.returnRemappingRows(map)
}
    } // end of while loop
  }

  

  /** Process the information about secondary induced transitions. */
  @inline private def processSecondaryInducedNewEffectOnStore(
    secondaryInduced: SecondaryInducedInfo)
  = {
    require(useNewEffectOnStore)
    var index = 0
    while(index < secondaryInduced.length){
      val (mapX, rrParams, linkages, unifs, k) = secondaryInduced(index); 
      index += 1
      val allCompletions = 
        if(false) List(mapX) else sreou.allCompletions(rrParams, mapX, linkages)
for(map <- allCompletions){
      val cpts = mkComponents(map) 
      Profiler.count("SecondaryInduced")
      val crossRefs: List[Array[State]] =
        getCrossRefs(pre.servers, cpts, pre.components)
      val newPrinc = getNewPrinc(cpts(0), unifs)
      val newComponentsList = List(StateArray(Array(postCpts(k), newPrinc)))
      processInducedInfoNewEffectOnStore(
        map, cpts, unifs, null, false, crossRefs, newComponentsList) 
        // , rrParams, linkages)
      // processInducedInfo(map, cpts, unifs, null, false, crossRefs, 
      //   newComponentsList, rrParams, linkages)
}
    }
  }



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
              addedView(cpts, newCpts, nv, unifs, isPrimary, reducedMap)
            else recordInducedRedundant(
              cpts, newCpts, nv, unifs, isPrimary, reducedMap)
          }
          else newEffectOnStore.add(mcw)
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


}

// =======================================================

object NewEffectOn{
  @inline private def guard = singleRef && useNewEffectOnStore

  var newEffectOnStore: NewEffectOnStore =
    if(guard) new NewEffectOnStore else null

  def reset = {
    if(guard)
      newEffectOnStore = new NewEffectOnStore
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
      SingleRefEffectOn.tryAddView(nv, nextNewViews)
    }
  }

  def report = {
    require(guard);  newEffectOnStore.report
  }

  /** Perform a memory profile of this. */
  def memoryProfile = {
    require(guard)
    import ox.gavin.profiling.MemoryProfiler.traverse
    // if(effectOnStore != null){
    //   effectOnStore.report; println()
    //   effectOnStore.memoryProfile
    // }
    // if(newEffectOnStore != null) 
    newEffectOnStore.memoryProfile
    traverse("NewEffectOn", this, maxPrint = 1, ignore = List("System"))
  }
}
