package ViewAbstraction

import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.Remapper

import scala.collection.mutable.{ArrayBuffer}

/** A utility object, encapsulating the effectOn and completeDelayed
  * functions.  These describe the effect that one transition has on another
  * View. */
class EffectOn(views: ViewSet, system: SystemP.System){
  /* Overview of main functions.
   * 
   * apply
   * |--getCrossReferences
   * |--EffectOnUnification.apply
   * |--processInducedInfo
   * |  |--checkCompatibleMissing
   * |  |--missingCrossRefs
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
  private val effectOnStore: EffectOnStore = new SimpleEffectOnStore

  import Unification.UnificationList //  = List[(Int,Int)]

  import ComponentView.ReducedMap 

  /** The effect of the transition pre -e-> post on cv.  Create extra views
    * caused by the way the transition changes cv, and add them to
    * nextNewViews. */
  def apply(
    pre: Concretization, e: EventInt, post: Concretization, cv: ComponentView, 
    nextNewViews: MyHashSet[ComponentView])
  = {
    require(pre.servers == cv.servers) // && pre.sameComponentPids(post)
    val postCpts = post.components; val preCpts = pre.components
// IMPROVE
    val highlight = false // preCpts(0).cs == 6 && postCpts(0).cs == 7
      // pre.servers.servers(1).cs == 100 && post.servers.servers(5).cs == 113 &&
      // preCpts.length == 2 && cv.components.length == 2 &&
      // preCpts(0).cs == 66 && preCpts(1).cs == 13 && preCpts(1).ids(2) == 3 &&
      //   preCpts.sameElements(cv.components)
    // if(highlight) println("********")
    if(showTransitions || highlight) println(s"EffectOn($pre, $post, $cv)")

    // inducedInfo: ArrayBuffer[(RemappingMap, Array[State], UnificationList)
    // is a set of triples (pi, pi(cv.cpts), unifs) where pi is a unification
    // function corresponding to unifs. secondaryInducedArray:
    // Buffer[(Array[State], UnificationList, Int) is similar for secondary
    // induced transitions, where the final component is the index of
    // preCpts/postCpts that gains a reference to cv.principal.
    val (inducedInfo, secondaryInduced)
        : (ArrayBuffer[
            (RemappingMap, Array[State], UnificationList, ReducedMap)],
           ArrayBuffer[(Array[State], UnificationList, Int)]) =
      if(singleRef && newEffectOn)
        new SingleRefEffectOnUnification(pre,post,cv)()
      else EffectOnUnification.combine(pre, post, cv)
    //if(highlight) println("secondaryInduced length: "+secondaryInduced.length)

    /* Function to process induced transition. */
    val processInducedInfo1 = 
      processInducedInfo(pre, e, post, cv, nextNewViews) _
    /* What does cpt get mapped to given unifications unifs? */
    @inline def getNewPrinc(cpt: State, unifs: UnificationList): State = {
      var us = unifs; while(us.nonEmpty && us.head._1 != 0) us = us.tail
      if(us.isEmpty) cpt else postCpts(us.head._2)
    }
    // Process inducedInfo
    var index = 0
    while(index < inducedInfo.length){
      val (map, cpts, unifs, reducedMapInfo) = inducedInfo(index); index += 1
// IMPROVE: understand why there are repetitions; it might be RemappingExtender.allExtensions.
      // Test if this value appears again later.
      if(true) for(i <- index until inducedInfo.length){
        val (map1,cpts1,unifs1,reducedMapInfo1) = inducedInfo(i)
        if(cpts1.sameElements(cpts) && unifs1 == unifs){
          if(newEffectOn) Profiler.count("Induced repetition")
          else assert(false,
            s"pre = $pre\npost = $post\ncv = $cv\n"+
              "map = "+Remapper.show(map)+"\nmap1 = "+Remapper.show(map1)+
              "\ncpts = "+StateArray.show(cpts)+s"\nunifs = $unifs" )
        }
      }
      Profiler.count("EffectOn step "+unifs.isEmpty)
      // The components needed for condition (b).
      val crossRefs: List[Array[State]] = 
        if(singleRef) getCrossRefs(pre.servers, cpts, pre.components)
        else List()
      if(reducedMapInfo == null ||
         !cv.containsConditionBInduced(post.servers, reducedMapInfo, crossRefs)){
        val newPrinc = getNewPrinc(cpts(0), unifs)
        var newComponentsList =
          StateArray.makePostComponents(newPrinc, postCpts, cpts)
        processInducedInfo1(
          map, cpts, unifs, reducedMapInfo, true, crossRefs, newComponentsList)
      }
    } // end of while loop
    // Process secondaryInduced
    index = 0
    while(index < secondaryInduced.length){
      val (cpts, unifs, k) = secondaryInduced(index); index += 1
      Profiler.count("SecondaryInduced")
      // if(highlight) println("***secondaryInduced: "+StateArray.show(cpts))
      val crossRefs: List[Array[State]] = 
        if(singleRef) getCrossRefs(pre.servers, cpts, pre.components)
        else List()
      val newPrinc = getNewPrinc(cpts(0), unifs) 
      val newComponentsList = List(Array(postCpts(k), newPrinc))

      // if(highlight) println("newComponentsList: "+
      //   newComponentsList.map(StateArray.show).mkString("\n"))
      processInducedInfo1(
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
    pre: Concretization,  e: EventInt, post: Concretization,
    cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
    (map: RemappingMap, cpts: Array[State], unifs: UnificationList, 
      reducedMap: ReducedMap, isPrimary: Boolean, crossRefs: List[Array[State]],
      newComponentsList: List[Array[State]])
  : Unit = {
    val highlight = false//  && // IMPROVE
      // pre.servers.servers(1).cs == 99 &&
      // pre.components(0).cs == 59 && pre.components(1).cs == 37 &&
      // cv.components(0).cs == 10 && cv.components(1).cs == 14
    if(debugging){
      StateArray.checkDistinct(cpts); assert(cpts.length==cv.components.length)
    }
    if(showTransitions && isPrimary || highlight) 
      println("processInducedInfo: "+Remapper.show(map))
    // Record this induced transition if singleRef, if primary and no unifs
    @inline def recordInduced(): Boolean = {
      if(singleRef && isPrimary && unifs.isEmpty)
        cv.addDoneInducedPostServersRemaps(post.servers, reducedMap)
      else true
    }
    // Show the transition
    @inline def showTransition(newComponents: Array[State], nv: ComponentView)
    = println(
        s"$pre -${system.showEvent(e)}->\n  $post\n"+
          s"  with unifications $unifs, isPrimary == $isPrimary\n  induces $cv\n"+
          (if(!cv.components.sameElements(cpts))
            s"  == ${View.show(pre.servers, cpts)}\n"
          else "")+
          s"  --> ${View.show(post.servers, newComponents)}\n"+
          (if(post.servers != nv.servers ||
            !newComponents.sameElements(nv.components))
            s"  ==  $nv"
          else "")
    )
    // Show information about a redundancy
    @inline def showRedundancy(
      v1: => ComponentView, newComponents: Array[State], nv: ComponentView)
    = {
      Profiler.count("EffectOn redundancy:"+isPrimary+unifs.isEmpty)
      if(showRedundancies){ // give information about redundancies
        //val v1 =  if(thisPly) nextNewViews.get(nv) else views.get(nv)
        if(v1.inducedFrom(cv)){
          showTransition(newComponents, nv)
          // println(s"$pre -${system.showEvent(e)}-> $post\n"+
          //   s"  with unifications $unifs induces $cv --> $nv\n"+
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
    val missing: List[ComponentView] =
      crossRefs.map(new ComponentView(pre.servers, _)).filter(!views.contains(_))
    for(newComponents <- newComponentsList){
      val nv = Remapper.mkComponentView(post.servers, newComponents)
      // if(highlight){
      //   println("processInducedInfo: "+StateArray.show(newComponents))
      //   println(s"nv = $nv"); println(views.contains(nv))
      //   println("missing = "+missing+"\nmissingCommons = "+missingCommons)
      // }
      Profiler.count("newViewCount") 
      if(!views.contains(nv)){
        if(missing.isEmpty && missingCommons.isEmpty && nextNewViews.add(nv)){
          Profiler.count("addedViewCount")
          if(showTransitions) showTransition(newComponents, nv)
          nv.setCreationInfoIndirect(pre, cpts, cv, e, post, newComponents)
          val ok = recordInduced() 
          if(false && singleRef && isPrimary && unifs.isEmpty){
            val ok = cv.addDoneInduced(post.servers); assert(ok)
          }
          //if(!ok) println(s"not ok  $cv $pre $post\n"+reducedMap.mkString(", "))
          // assert(ok) I think this can fail if there are two similar cases
          //in this batch
          if(!nv.representableInScript){
            println("Not enough identities in script to combine transition\n"+
              s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
            sys.exit
          }
        } // end of if(missing.isEmpty && nextNewViews.add(nv))
        else if(missing.nonEmpty || missingCommons.nonEmpty){
          // Note: we create nv eagerly, even if missing is non-empty: this
          // might not be the most efficient approach.  Note also that the
          // missingCommons may be shared.
          effectOnStore.add(missing, missingCommons, nv)
          assert(missing.isEmpty || !views.contains(missing.head))
          Profiler.count(s"EffectOn add to store-$isPrimary-${unifs.nonEmpty}"+
            s"-${pre.servers==post.servers}-${missing.nonEmpty}-"+
            missingCommons.nonEmpty)
          nv.setCreationInfoIndirect(pre, cpts, cv, e, post, newComponents)
// IMPROVE: do we need to check isPrimary here? 
          if(isPrimary && reducedMap != null && missingCommons.isEmpty){
            val ok = cv.addConditionBInduced(post.servers, reducedMap, crossRefs)
            assert(ok)
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
  }



  /** Test whether, if the principal components of cpts1 and cpts2 both have a
    * reference to the same missing component then there is a way of
    * instantiating that component, consistent with the current set of views.
    * @return the identities of all such missing components. */ 
  private def checkCompatibleMissing(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
      : List[MissingCommon]  = {
    require(singleRef)
    val missingRefs1 = StateArray.missingRefs(cpts1)
    val missingRefs2 = StateArray.missingRefs(cpts2)
    // The common references considered so far for which there is no way of
    // instantiating the referenced component.
    var missingCommonRefs = List[ProcessIdentity]()
    var missingCommons = List[MissingCommon]()
    for(pid <- missingRefs1; if missingRefs2.contains(pid)){
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
    } // end of for loop
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

/*
  /** Missing cross references, if singleRef.  For each reference from a
    * component c1 of cpts2 to a component c2 of cpts2, or vice versa, test if
    * sysAbsViews contains the view servers || c1 || c2.  Return all such
    * missing views.  (cpts1 corresponds to cv.components; cpts2 corresponds
    * to pre.components). */
  @inline private def missingCrossRefs(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
      : List[ComponentView] = {
    assert(singleRef)
    var missing = List[ComponentView]() // missing necessary Views
    for(cptsx <- StateArray.crossRefs(cpts1, cpts2)){
      val cvx = Remapper.mkComponentView(servers, cptsx)
      if(!views.contains(cvx)) missing ::= cvx
    }
    if(verbose && missing.nonEmpty) 
      println(s"missingCrossRefs(${StateArray.show(cpts1)}, "+
        s"${StateArray.show(cpts2)}):\n  $missing")
    missing
  }
 */

  /** If cv completes a delayed transition in effectOnStore, then complete it. */
  def completeDelayed(cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
  = {
    for(nv <- effectOnStore.complete(cv, views)){
      if(showTransitions) println(s"Adding $nv from completeDelayed($cv)")
      tryAddView(nv, nextNewViews)
    }
  }

  /** Add mi.nextNewViews to nextNewViews. */
  @inline private 
  def tryAddView(nv: ComponentView, nextNewViews: MyHashSet[ComponentView]) = {
    // require(mi.done); val nv = mi.newView
    if(nextNewViews.add(nv)){
      if(showTransitions){
        val (pre, cpts, cv, post, newComponents) = nv.getCreationIngredients
        println(s"Adding via completeDelayed $cv -> $nv\n"+
          s"$pre --> $post\n"+
          s"  induces $cv == ${View.show(pre.servers, cpts)}\n"+
          s"  --> ${View.show(post.servers, newComponents)} == $nv")
      }
      if(!nv.representableInScript){
        val (pre, cpts, cv, post, newComponents) = nv.getCreationIngredients
        println("Not enough identities in script to combine transition\n"+
          s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
        sys.exit
      }
    } // end of outer if
  }

  def sanityCheck = effectOnStore.sanityCheck(views)

  def report = effectOnStore.report

}
