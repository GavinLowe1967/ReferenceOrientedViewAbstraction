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

  /* Overview of main function.
   * 
   * apply
   * |--SingleRefEffectOnUnification.apply
   * |--processPrimaryInduced
   * |  |-processInducedInfo
   * |   |  |--checkCompatibleMissing
   * |   |  |--EffectOn.effectOnStore.add
   * |--processSecondaryInduced
   * |  |--getCrossRefs
   * |  |--processInducedInfo (as above)
   */

  import ServersReducedMap.ReducedMap 
  import Unification.UnificationList //  = List[(Int,Int)]
  import SingleRefEffectOnUnification.{InducedInfo, SecondaryInducedInfo, commonMissingRefs}
  import SingleRefEffectOn.{getCrossRefs, effectOnStore}
  import EffectOn.views

  /** The effect of the transition t on cv.  Create extra views caused by the
    * way the transition changes cv, and add them to nextNewViews. */
  override def apply() : Unit = {
    assert(!useNewEffectOnStore)
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
      val sreou = new SingleRefEffectOnUnification(trans,cv)
      val (inducedInfo, secondaryInduced): (InducedInfo,SecondaryInducedInfo) =
        sreou()
      processPrimaryInduced(inducedInfo);
      processSecondaryInduced(secondaryInduced)
    }
  }

  /** Process the information about primary induced transitions. */
  @inline private def processPrimaryInduced(inducedInfo: InducedInfo) = {
    assert(singleRef && !useNewEffectOnStore)
    var index = 0
    while(index < inducedInfo.length){
      // Note: we ignore the candidates component here
      val (map, _, unifs, reducedMapInfo) = inducedInfo(index); index += 1
      Profiler.count("EffectOn step "+unifs.isEmpty)
      val cpts =  Remapper.applyRemapping(map, cv.components)
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
        processInducedInfo(cpts, unifs, reducedMapInfo, true, crossRefs, 
          newComponentsList)

      }
      Pools.returnRemappingRows(map)
    } // end of while loop
  }

  /** Process the information about secondary induced transitions. */
  @inline private
  def processSecondaryInduced(secondaryInduced: SecondaryInducedInfo)  = {
    require(!useNewEffectOnStore)
    var index = 0
    while(index < secondaryInduced.length){
      val (map, _, unifs, k) = secondaryInduced(index); index += 1
      val cpts = Remapper.applyRemapping(map, cv.components) 
      Profiler.count("SecondaryInduced")
      val crossRefs: List[Array[State]] =
        getCrossRefs(pre.servers, cpts, pre.components)
      val newPrinc = getNewPrinc(cpts(0), unifs)
      val newComponentsList = List(StateArray(Array(postCpts(k), newPrinc)))
      processInducedInfo(cpts, unifs, null, false, crossRefs, 
        newComponentsList)
    }
  }

  /** Create induced transition producing views with post.servers and each
    * element of newComponentsList.  The transition is induced by pre -e->
    * post acting on cv, with unifications unifs; cv.cpts is remapped to
    * produce cpts.  This creates cross references for condition (b)
    * corresponding to crossRefs.  The induced transition, if possible, will
    * produce views corresponding to newComponentList. Add result to
    * nextNewViews.
    * 
    * This function would live better inside apply; but that function is too
    * large.  Most other parameters are as there (most are used only for
    * setting creation information or textual output).
    * @param isPrimary are we creating a primary transition?
    * @param reducedMap a representation of the RemappingMap |> post.servers. */
  @inline private def processInducedInfo(
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
            addedView(cpts, newComponents, nv, unifs, isPrimary, reducedMap)
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

  // ---------- Generic helper functions
  // Also used in NewEffectOn

  /** Actions performed when a new view has been added to the view set,
    * principally setting the creation information. */
  @inline protected def addedView(
    cpts: Array[State], newComponents: Array[State], nv: ComponentView,
    unifs: UnificationList, isPrimary: Boolean, reducedMap: ReducedMap)
  = {
    //if(highlight) println("added")
    Profiler.count("addedViewCount")
    if(showTransitions || ComponentView0.highlight(nv))
      showTransition(cpts, newComponents, nv, unifs, isPrimary)
    nv.setCreationInfoIndirect(trans, cpts, cv, newComponents)
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
 
  /** Record the induced transition, and show it was redundant. */
  @inline protected def recordInducedRedundant(
    cpts: Array[State], newComponents: Array[State], nv: ComponentView,
    unifs: UnificationList, isPrimary: Boolean, reducedMap: ReducedMap)
  = {
    assert(singleRef)
    if(isPrimary) recordInduced(unifs, reducedMap)
    showRedundancy(views.get(nv), cpts, newComponents, nv, unifs, isPrimary)
  }

  // ------------------------------ Helper functions for conditions (b) and (c)

  /** The missing cross reference views required for condition (b). */
  @inline protected def missingCrossRefs(crossRefs: List[Array[State]])
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
  @inline private def guard = singleRef && !useNewEffectOnStore

  /* Overview of main functions.
   * 
   * completeDelayed
   * |--EffectOnStore.complete
   * |--tryAddNewView (also used in NewEffectOn)
   * 
   * getCrossRefs
   * |--StateArray.crossRefs
   * 
   * reset, prepareForPurge, purge, sanityCheck, report, memoryProfile
   */

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

  def reset = { 
    if(guard)  effectOnStore = new SimpleEffectOnStore
    lastPurgeViewCount = 0L; doPurge = false
  }

  import EffectOn.{views}

  /** If cv completes a delayed transition in effectOnStore, then complete it. */
  def completeDelayed(cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
  = {
    require(guard)
    val newViews = effectOnStore.complete(cv, views)
    for(nv <- newViews){
      if(showTransitions || ComponentView0.highlight(nv)) 
        println(s"Adding $nv\n from completeDelayed($cv)")
      tryAddView(nv, nextNewViews)
    }
  }

  /** Add mi.nextNewViews to nextNewViews. 
    * Also used in NewEffectOn. */
  @inline // private 
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

  /* ---- Helper functions for conditions (b) and (c). ---------- */

  /** Get (the components of) the cross reference views between cpts1 and cpts2,
    * needed for condition (b). */
  @inline def getCrossRefs(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
      : List[Array[State]] = {
    assert(singleRef)
    StateArray.crossRefs(cpts1, cpts2).map(Remapper.remapComponents(servers,_))
  }

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
  def prepareForPurge = {
    doPurge = testPurge
    if(doPurge){  
      effectOnStore.prepareForPurge; MissingCommon.prepareForPurge
    }
  }

  /* --------- Supervisory functions. */

  def sanityCheck = effectOnStore.sanityCheck(views)

  def report = { require(guard); effectOnStore.report }

  /** Perform a memory profile of this. */
  def memoryProfile = {
    require(guard)
    import ox.gavin.profiling.MemoryProfiler.traverse
    effectOnStore.report; println()
    effectOnStore.memoryProfile
    traverse("SingleRefEffectOn", this, maxPrint = 1, ignore = List("System"))
  }
}
