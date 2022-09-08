package ViewAbstraction

import collection.MyHashSet
import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.Remapper

import scala.collection.mutable.{ArrayBuffer}

/** A utility object, encapsulating the effectOn and completeDelayed
  * functions.  These describe the effect that one transition has on another
  * View. */
object EffectOn{
  /** The current set of views.  Set by init. */
  private var views: ViewSet = null

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
  private var effectOnStore: EffectOnStore = 
    if(singleRef) new SimpleEffectOnStore else null

  def reset = { 
    effectOnStore = if(singleRef) new SimpleEffectOnStore else null 
    lastPurgeViewCount = 0L; doPurge = false
  }

  import Unification.UnificationList //  = List[(Int,Int)]

  import ServersReducedMap.ReducedMap 

  // private def highlight(cv: ComponentView) =
  //   ComponentView0.highlightServers(cv.servers) && 
      // //  44(T2,N5,N6) or 45(T2,N5,N6)
      // ComponentView0.highlightPrinc(cv.components(0)) && {
      //   val second = cv.components(1)
      //   // 16|17(N6,_,N4,N2)
      //   (second.cs == 17 || second.cs == 16) &&
      //   second.ids(0) == 5 && second.ids(2) == 3 && second.ids(3) == 1
      // }

  /** If cv completes a delayed transition in effectOnStore, then complete it. */
  def completeDelayed(cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
  = {
    // if(highlight(cv)) println(s"completeDelayed($cv)")
    for(nv <- effectOnStore.complete(cv, views)){
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
        val (pre, cpts, cv, post, newComponents) = nv.getCreationIngredients
        println(s"Adding via completeDelayed \n"+
          s"$pre\n  --> $post induces \n"+
          EffectOnStore.showInduced(cv, cpts, post.servers, newComponents, nv))
      }
      if(!nv.representableInScript){
        val (pre, cpts, cv, post, newComponents) = nv.getCreationIngredients
        println("Not enough identities in script to combine transition\n"+
          s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
        sys.exit()
      }
    } // end of outer if
  }

  /* Purging of effectOnStore.  This is done according to certain heuristics. */

  /** The number of views when last we did a purge. */
  private var lastPurgeViewCount = 0L

  /** Only purge if at least purgeQuantum views have been added since the last
    * round of purges. */
  private val PurgeQuantum = 300_000

  /** Is it time for another purge? */
  private var doPurge = false

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
    // round: at least PurgeQuantum and 25% of the total.
    val viewCount = views.size; val newViewCount = viewCount-lastPurgeViewCount
    if(newViewCount >= PurgeQuantum && 4*newViewCount >= viewCount){
      println("Preparing for purge")
      doPurge = true; lastPurgeViewCount = viewCount
      effectOnStore.prepareForPurge; MissingCommon.prepareForPurge
    }
    else doPurge = false
  }

  def sanityCheck = effectOnStore.sanityCheck(views)

  def report = effectOnStore.report

  /** Perform a memory profile of this. */
  def memoryProfile = {
    import ox.gavin.profiling.MemoryProfiler.traverse
    if(effectOnStore != null){
      effectOnStore.report; println()
      effectOnStore.memoryProfile
    }
    traverse("effectOn", this, maxPrint = 1, ignore = List("System"))
  }
}

// ==================================================================

/** Object to calculate the effect of the transition t on cv.  Create extra
    * views caused by the way the transition changes cv, and add them to
    * nextNewViews. */
class EffectOn(
  trans: Transition, cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
{
  /* Overview of main function.
   * 
   * apply
   * |--getCrossReferences
   * |--EffectOnUnification.apply
   * |--processInducedInfo
   * |  |--checkCompatibleMissing
   * |  |--missingCrossRefs
   */

  import Unification.UnificationList //  = List[(Int,Int)]

  import ServersReducedMap.ReducedMap 

  import SingleRefEffectOnUnification.{InducedInfo, SecondaryInducedInfo}
  // InducedInfo = 
  //   ArrayBuffer[(RemappingMap, Array[State], UnificationList, ReducedMap)]
  // SecondaryInducedInfo = ArrayBuffer[(Array[State], UnificationList, Int)]

  private val pre = trans.pre; private val post = trans.post
  private val postCpts = post.components;

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

  /** Do pre and cv have the same secondary component, or both missing a
    * secondary component?  Assumes they have the same principal, so pre has
    * at least as many components as cv. */
  // private def matchingSecondaries = 
  //   cv.components.length == 1 || pre.components(1) == cv.components(1)

  // if(pre.components(0) == cv.components(0) && 
  //     (!singleRef || matchingSecondaries))
  //   println(s"Matching views in EffectOn:\n$trans\n$cv") 

  /** What does cpt get mapped to given unifications unifs? */
  private def getNewPrinc(cpt: State, unifs: UnificationList): State = {
    var us = unifs; while(us.nonEmpty && us.head._1 != 0) us = us.tail
    if(us.isEmpty) cpt else postCpts(us.head._2)
  }
  
  import EffectOn.views

  /** The effect of the transition t on cv.  Create extra views caused by the
    * way the transition changes cv, and add them to nextNewViews. */
  def apply() : Unit = {
    // Early bail-out if servers don't change, no chance of unification with
    // components that change state, and no chance of secondary induced
    // transitions.  This captures over about 25% of cases with lazySet.csp,
    // bound 44; nearly all other cases have servers that change state.
    if(trans.mightGiveSufficientUnifs(cv)){
      if(highlight) println("mightGiveSufficientUnifs")
      // inducedInfo: ArrayBuffer[(RemappingMap, Array[State], UnificationList,
      // ReducedMap)] is a set of tuples (pi, pi(cv.cpts), unifs, reducedMap)
      // where pi is a unification function corresponding to
      // unifs. secondaryInducedArray: Buffer[(Array[State], UnificationList,
      // Int) is similar for secondary induced transitions, where the final
      // component is the index of preCpts/postCpts that gains a reference to
      // cv.principal.
      val (inducedInfo, secondaryInduced): (InducedInfo, SecondaryInducedInfo) =
        if(singleRef) new SingleRefEffectOnUnification(trans,cv)()
        else EffectOnUnification.combine(trans, cv)
      //if(highlight) println("inducedInfo.length == "+inducedInfo.length)
      processInduced(inducedInfo)
      processSecondaryInduced(secondaryInduced)
    }
    else if(highlight)
      println(s"Not sufficient unifs: "+cv.containsDoneInduced(post.servers))
  }

  /** Process the information about primary induced transitions. */
  @inline private def processInduced(inducedInfo: InducedInfo) = {
    var index = 0
    while(index < inducedInfo.length){
      val (map, cpts, unifs, reducedMapInfo) = inducedInfo(index); index += 1
      // val hl = highlight && map(0).sameElements(Array(0,4,5,2,3)) &&
      //   map(1).sameElements(Array(0,2,3))
      // if(hl)
      //   println(s"unifs = $unifs\ncpts = "+StateArray.show(cpts)+
      //     "\nmap = "+Remapper.show(map))
      Profiler.count("EffectOn step "+unifs.isEmpty)
      // The components needed for condition (b).
      val crossRefs: List[Array[State]] =
        if(singleRef) getCrossRefs(pre.servers, cpts, pre.components)
        else List()
// IMPROVE.  Turning off optimisation
      if(unifs.nonEmpty || reducedMapInfo == null ||
        !cv.containsConditionBInduced(post.servers, reducedMapInfo, crossRefs)){
        val newPrinc = getNewPrinc(cpts(0), unifs)
        var newComponentsList =
          StateArray.makePostComponents(newPrinc, postCpts, cpts)
        // if(hl || false && highlight)
        //   println("newComponentList: "+newComponentsList.map(StateArray.show))
        processInducedInfo(
          map, cpts, unifs, reducedMapInfo, true, crossRefs, newComponentsList)
      }
      // else if(hl) println(
      //   s"*** reducedMapInfo = ${reducedMapInfo.mkString(",")}; "+
      //     cv.containsConditionBInduced(post.servers, reducedMapInfo, crossRefs)+
      //     "; crossRefs = "+crossRefs.map(StateArray.show).mkString("; "))
    } // end of while loop
  }

  /** Process the information about secondary induced transitions. */
  @inline private 
  def processSecondaryInduced(secondaryInduced: SecondaryInducedInfo)  = {
    var index = 0
    while(index < secondaryInduced.length){
      val (cpts, unifs, k) = secondaryInduced(index); index += 1
      Profiler.count("SecondaryInduced")
      val crossRefs: List[Array[State]] =
        if(singleRef) getCrossRefs(pre.servers, cpts, pre.components)
        else List()
      val newPrinc = getNewPrinc(cpts(0), unifs)
      val newComponentsList = List(Array(postCpts(k), newPrinc))
      processInducedInfo(
        null, cpts, unifs, null, false, crossRefs, newComponentsList)
    }
  }

  /** Create induced transition producing views with post.servers and each
    * element of newComponentsList.  The transition is induced by pre -e->
    * post acting on cv, with unifications unifs; cv.cpts is remapped by map
    * to produce cpts.  Add result to nextNewViews.
    * 
    * This function would live better inside apply; but that function is too
    * large.  Most other parameters are as there (most are used only for
    * setting creation information or textual output).
    * @param isPrimary are we creating a primary transition?
    * @param reducedMap a representation of map |> post.servers. */
  @inline private 
  def processInducedInfo(
    map: RemappingMap, cpts: Array[State], unifs: UnificationList, 
    reducedMap: ReducedMap, isPrimary: Boolean, crossRefs: List[Array[State]],
    newComponentsList: List[Array[State]])
      : Unit = {
    Profiler.count(s"processInducedInfo $isPrimary")
    // StateArray.checkDistinct(cpts); assert(cpts.length==cv.components.length)
    val highlight1 = highlight && map(0).sameElements(Array(0,1,3,2))
    if(highlight1) 
      println("processInducedInfo: "+unifs+"; "+Remapper.show(map)+
        "; cpts = "+StateArray.show(cpts))

    /* Record this induced transition if singleRef and primary, and (1) if
     * newEffectOn, no acquired references, (2) otherwise no unifs. */
    @inline def recordInduced() = if(singleRef && isPrimary){ // and newEffectOn
      // IMPROVE: repeats work from SingleRefEffectOnUnification:
      // doesPrincipalAcquireRef and getPostUnified.  
      if(StoreDoneInducedPostServersRemaps){ // currently true
        if(DetectRepeatRDMapWithUnification){ // currently false
          if(!trans.doesPrincipalAcquireRef(unifs))
            cv.addDoneInducedPostServersRemaps(post.servers, reducedMap,
              trans.getPostUnified(unifs, cv.components.length) )
        }
        else if(unifs.isEmpty) // old version
          cv.addDoneInducedPostServersRemaps(post.servers, reducedMap)
      }
      // Record that we've done a transition on cv with these post servers
      // and no unifications
      if(!trans.isChangingUnif(unifs) && !trans.serverGetsNewId)
        cv.addDoneInduced(post.servers)
    }

    /* Show the transition. */
    @inline def showTransition(newComponents: Array[State], nv: ComponentView)
    = println(s"$trans\n  with unifications $unifs, isPrimary == $isPrimary\n"+
      "  induces "+
      EffectOnStore.showInduced(cv, cpts, post.servers, newComponents, nv)
    )

    /* Show information about a redundancy. */
    @inline def showRedundancy(
      v1: => ComponentView, newComponents: Array[State], nv: ComponentView)
    = {
      Profiler.count("EffectOn redundancy:"+isPrimary+unifs.isEmpty)
      if(showRedundancies){ // give information about redundancies
        if(v1.inducedFrom(cv)){
          showTransition(newComponents, nv)
          println(s"Previously "+v1.showCreationInfo+"\n")
        }
      }
    }

    // If singleRef, identities of components referenced by both principals,
    // but not included in the views, and such that there is no way of
    // instantiating them consistently within sysAbsViews.
    val missingCommons: List[MissingCommon] =
      if(singleRef && !pre.components.sameElements(cv.components))
        checkCompatibleMissing(pre.servers, pre.components, cpts)
      else List()
    // If singleRef and there are references between components from pre and
    // cv, then check that that combination is possible in sysAbsViews:
    // those that are missing.
    val missing: List[ReducedComponentView] =
      crossRefs.map{ cpts => ReducedComponentView(pre.servers, cpts) }.
        // Profiler.count("ReducedComponentView: EffectOn")
        filter(!views.contains(_))
    for(newComponents <- newComponentsList){
      if(highlight1) 
        println(s"unifs = $unifs; newComponents = "+
          StateArray.show(newComponents))
      val nv = Remapper.mkComponentView(post.servers, newComponents)
      Profiler.count("newViewCount") 
      if(!views.contains(nv)){
        if(missing.isEmpty && missingCommons.isEmpty && nextNewViews.add(nv)){
          if(highlight) println("added")
          Profiler.count("addedViewCount")
          if(showTransitions || ComponentView0.highlight(nv)) 
            showTransition(newComponents, nv)
          nv.setCreationInfoIndirect(pre, cpts, cv, trans.e, post, newComponents)
          recordInduced() 
          // Following superceded by recordInduced
          // if(false && singleRef && isPrimary && unifs.isEmpty){
          //   val ok = cv.addDoneInduced(post.servers); assert(ok)
          // }
          if(!nv.representableInScript){
            println("Not enough identities in script to combine transition\n"+
              s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
            sys.exit()
          }
        } // end of if(missing.isEmpty && nextNewViews.add(nv))
        else if(missing.nonEmpty || missingCommons.nonEmpty){
          if(highlight1) 
            println(s"missing = $missing\nmissingCommons = $missingCommons")
          // Note: we create nv eagerly, even if missing is non-empty: this
          // might not be the most efficient approach.  Note also that the
          // missingCommons may be shared.
          EffectOn.effectOnStore.add(missing, missingCommons, nv, trans,
            /*pre,*/ cpts, cv, /*trans.e, post,*/ newComponents)
          assert(missing.isEmpty || !views.contains(missing.head))
          // Profiler.count(s"EffectOn add to store-$isPrimary-${unifs.nonEmpty}"+
          //   s"-${pre.servers==post.servers}-${missing.nonEmpty}-"+
          //  missingCommons.nonEmpty)
          nv.setCreationInfoIndirect(pre, cpts, cv, trans.e, post, newComponents)
// IMPROVE: do we need to check isPrimary here? 
          if(isPrimary && unifs.isEmpty && missingCommons.isEmpty){
            val ok = cv.addConditionBInduced(post.servers, reducedMap, crossRefs)
            // assert(ok) // fails with concurrency
          }
        }
        else{ // nv was in nextNewViews 
          recordInduced() // might give false
          showRedundancy(nextNewViews.get(nv), newComponents, nv)
        }
      } // end of if(!views.contains(nv))
      // Try to work out why so many cases are redundant
      else{ // views already contains nv
        recordInduced()
        showRedundancy(views.get(nv), newComponents, nv)
      }
    } // end of for loop
  } // end of processInducedInfo

  /** Test whether, if the principal components of cpts1 and cpts2 both have a
    * reference to the same missing component then there is a way of
    * instantiating that component, consistent with the current set of views.
    * @return the identities of all such missing components. */ 
  private def checkCompatibleMissing(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
      : List[MissingCommon]  = {
    require(singleRef)
    var missingRefs1: List[ProcessIdentity] = StateArray.missingRefs(cpts1)
    val missingRefs2: List[ProcessIdentity] = StateArray.missingRefs(cpts2)
    // The common references considered so far for which there is no way of
    // instantiating the referenced component.
    var missingCommonRefs = List[ProcessIdentity]()
    var missingCommons = List[MissingCommon]()
    while(missingRefs1.nonEmpty){
      val pid = missingRefs1.head; missingRefs1 = missingRefs1.tail
      if(contains(missingRefs2, pid)){
        val mc = 
          MissingCommon.makeMissingCommon(servers, cpts1, cpts2, pid, views)
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
      }
    } // end of iteration over missingRefs1 for loop
    missingCommons
  }

  /** Get a representation of the cross references between cpts1 and cpts2,
    * needed for condition (b). */
  @inline private def getCrossRefs(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
      : List[Array[State]] = {
    assert(singleRef)
    StateArray.crossRefs(cpts1, cpts2).map(Remapper.remapComponents(servers,_))
  }
}
