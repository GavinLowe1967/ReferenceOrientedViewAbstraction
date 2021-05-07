package ViewAbstraction

import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.{Remapper,Unification}
import ViewAbstraction.CombinerP.Combiner
import ViewAbstraction.ExtendabilityP.Extendability
import scala.collection.mutable.{ArrayBuffer,HashSet,HashMap}
import java.util.concurrent.atomic.{AtomicLong,AtomicInteger,AtomicBoolean}


/** A checker for the view abstraction algorithm, applied to system.
  * @param aShapes the shapes of abstractions.
  * @param cShapes the shapes of concretizations. */
class Checker(system: SystemP.System){
  /** Exception thrown to indicate that an error transition has been found.
    * This is caught within process. */
  class FoundErrorException extends Exception

  // private var verbose = false 
  // private var veryVerbose = false

  /** The abstract views. */
  protected var sysAbsViews: ViewSet = null
  // Note: in various places, we iterate over sysAbsViews.  We should avoid
  // adding new views to the set while that is going on.

  /** The new views to be considered on the next ply. */
  protected var nextNewViews: MyHashSet[ComponentView] = null

  private var extendability: Extendability = _

  private var effectOnO: EffectOn = _

  private def showTransition(
    pre: Concretization, e: EventInt, post: Concretization) =
    s"$pre -${system.showEvent(e)}-> $post"

  val Million = 1000000

  private var done = new AtomicBoolean(false); protected var ply = 1

  import TransitionSet.Transition // (Concretization, EventInt, Concretization)

  /* A Transition is a tuple (pre, e, post): (Concretization, EventInt,
   * Concretization), representing the transition pre -e-> post.  The pre
   * state extends a View by adding all relevant components: components that
   * synchronise on the transition, and any components to which the principal
   * component obtains a reference.*/

  /** The extended transitions found on previous plies.  Abstractly, a set of
    * Transitions.  */
  private val transitions: TransitionSet = new ServerBasedTransitionSet(16)

  /** Transitions found on this ply.  Transitions are initially added to
    * newTransitions, but transferred to transitions at the end of the ply. */
  private var newTransitions: BasicHashSet[Transition] = null

  import TransitionTemplateSet.TransitionTemplate
  // = (Concretization, Concretization, ProcessIdentity, EventInt, Boolean)

  /* A TransitionTemplate (pre, post, id, e, include): (Concretization,
   * Concretization, ProcessIdentity, EventInt, Boolean) represents an
   * extended transition pre U st -e-> post U st' for every state st and st'
   * such that (1) st and st' have identity id; (2) st is compatible with pre;
   * (3) if include then st -e-> st', otherwise st = st'.  */

  /** The transition templates found on previous plies.  Abstractly, a set of
    * TransitionTemplates. */
  private val transitionTemplates: TransitionTemplateSet = 
    new ServerBasedTransitionTemplateSet

  /** Transition templates found on this ply.  Transition templates are
    * initially added to newTransitionTemplates, but transferred to
    * transitionsTemplates at the end of the ply. */
  private var newTransitionTemplates: MyHashSet[TransitionTemplate] = null

  /** A mapping showing which component views might be added later.  For each
    * cvx -> (missing, nv), once all of missing have been added, nv can also
    * be added. 
    * 
    * These are added in effectOn when a transition pre -> post induces a
    * transition cv -> nv, but where the views in missing represent
    * combinations of components from pre and cv that are not yet in the
    * store. 
    * 
    * Such a maplet is stored for each cvx in missing.  This might be
    * inefficient if missing is not a singleton: IMPROVE. */
  // private val effectOnStore = new SimpleEffectOnStore
  //  new HashMap[ComponentView, (List[ComponentView], ComponentView)]

  var addTransitionCount = 0L
  // var effectOfPreviousTransitionsCount = 0
  // var effectOnOthersCount = 0
  var newViewCount = 0L
  var addedViewCount = 0L
  // var effectOnRepetition = 0
  var instantiateTransitionTemplateCount = 0L
  // Counts on transition templates

  /** Store the ExtendedTransition pre -> post, and calculate its effect on
    * previously found views. */
  @inline private 
  def addTransition(pre: Concretization, e: EventInt, post: Concretization)
  = {
    addTransitionCount += 1
    assert(pre.ply < Int.MaxValue)
    assert(post.ply < Int.MaxValue)
    val newTrans = ((pre, e, post))
    if(!transitions.contains(newTrans)){
      if(newTransitions.add(newTrans)) effectOnOthers(pre, e, post)
    }
  }

  // ========= Processing a single view

  /** Process v, calculating all the concrete transitions from v, adding the
    * post-states to sysAbsViews, and adding new ones to nextNewViews.
    * @return true if a concrete transition on error is generated. 
    */
  private def process(v: View): Boolean = { 
    if(verbose) println(s"\n**** Processing $v")
    assert(v.ply < Int.MaxValue)
    v match{
      case cv: ComponentView =>
        for((pre, e, post, outsidePid) <- system.transitions(cv)){
          assert(pre.ply < Int.MaxValue)
          assert(post.ply == Int.MaxValue); post.ply = ply
          if(false)
            println(s"$pre -${system.showEvent(e)}-> $post ["+
              (if(outsidePid != null) State.showProcessId(outsidePid) else "")+
              "]")
          assert(pre.components(0) == cv.principal)
          // Find new views as a result of this transition
          try{ processTransition(pre, e, post, outsidePid) }
          catch{ 
            case _: FoundErrorException =>
              assert(e == system.Error); return true
          }
        } // end of for((pre, e, post, outsidePids) <- trans)
        // Effect of previous transitions on this view
        effectOfPreviousTransitions(cv)
        effectOfPreviousTransitionTemplates(cv)
        if(singleRef) effectOnO.completeDelayed(cv, nextNewViews)
    }
    false
  } 

  // ========= Processing a transition from a view.

  /** Process the transition pre -e-> post, creating the corresponding new views
    * and adding them to sysAbsViews and nextNewViews.  Add appropriate
    * TransitionTemplates and ExtendedTransitions to transitionTemplates and
    * transitions, respectively.
    * @param outsidePid if non-null, the identity of a component outside pre
    * that synchronises on the transition.  // FIXME: At most one?
    * @throw FoundErrorException is a concrete transition on error is
    * generated. */
  @inline private def processTransition(
    pre: Concretization, e: EventInt, post: Concretization, 
    outsidePid: ProcessIdentity) = {
    if(verbose) 
      println(s"processTransition:\n  $pre -${system.showEvent(e)}-> $post"+
        s" ($outsidePid)")
    val pids0 = pre.components(0).processIdentities
    val princ1 = post.components(0)
    // Process ids of other components
    val otherIds = pre.components.tail.map(_.componentProcessIdentity)
    assert(post.components.map(_.componentProcessIdentity).sameElements(
      pre.components.map(_.componentProcessIdentity)))
    // newPids is the components to which the principal component gains
    // references but that are outside pre/post.
    val newPids: Array[ProcessIdentity] =
      princ1.processIdentities.tail.filter(p =>
        !isDistinguished(p._2) && !otherIds.contains(p) && !pids0.contains(p))
    if(verbose) println(s"newPids = "+newPids.mkString(","))
    assert(newPids.length <= 1,    // simplifying assumption
      s"$pre -${system.showEvent(e)}-> $post:\n"+
        s"otherIds = ${otherIds.mkString(", ")}; "+
        s"newPids = ${newPids.mkString(", ")}")
    // The following assertion (outsidePid in newPids) captures an assumption
    // that the principal component cannot acquire a reference from nowhere:
    // the reference must be acquired either from another process in the view
    // or by synchronising with that other component.
    if(outsidePid != null) assert(newPids.head == outsidePid)

    if(newPids.isEmpty){
      // Case 1: no new nondistinguished parameter
      if(e == system.Error) throw new FoundErrorException
      // if(!newVersion) addViewFromConc(pre, e, post)
      // Store this transition, and calculate effect on other views.
      addTransition(pre, e, post)
    }
    else{ // Case 2: one new parameter from outside the view
      assert(newPids.length == 1) // simplifying assumption
      val newPid = newPids.head
      // Store transition template
      val newTransTemp = (pre, post, newPid, e, outsidePid != null)
      assert(!transitionTemplates.contains(newTransTemp)) // IMPROVE
      newTransitionTemplates.add(newTransTemp)
      // Try to find component of pre with non-omitted reference to newPid
      val preCpts = pre.components; val len = preCpts.length; 
      var i = 0; var done = false
      while(i < len && !done){
        // Test if preCpts(i) has non-omitted reference to newPid
        val cpt = preCpts(i); val pids = cpt.processIdentities; 
        val includeInfo = State.getIncludeInfo(cpt.cs); var j = 0
        while(j < pids.length && 
            (pids(j) != newPid || includeInfo != null && !includeInfo(j))) 
          j += 1
        if(j < pids.length) done = true
        else i += 1
      }
      if(i < len){
        instantiateTransitionTemplateViaRef(
          pre, post, newPid, e, outsidePid != null, preCpts(i))
      }
      else{
        // Counting of different types of TransitionTemplates; IMPROVE
        if(false){
          if(outsidePid != null) 
            Profiler.count("TransitionTemplate sync") // ~10%
          else{
            assert(pre.servers.servers.exists(
              _.processIdentities.contains(newPid)),
              s"pre = $pre; newPid = $newPid")
            Profiler.count("TransitionTemplate server") // ~30%
          }
        } // end of if(false)
        // Get extended transitions based on this
        instantiateTransitionTemplate(pre, post, newPid, e, outsidePid != null)
      }
    } // end of else
  }

  // ========= Extending TransitionTemplates 

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) based on prior views.
    * Called from processTransition. 
    * @throw FoundErrorException is a concrete transition on error is
    * generated. */
  private def instantiateTransitionTemplate(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean)  = {
    if(verbose) 
      println(s"instantiateTransitiontemplate($pre, $post, $newPid, "+
        s"${system.showEvent(e)}, $include)")
    Profiler.count("instantiateTransitionTemplate")
    val iter = sysAbsViews.iterator(pre.servers)
    while(iter.hasNext){
      val cv = iter.next
      instantiateTransitionTemplateBy(pre, post, newPid, e, include, cv)
    }
  }

  /** The effect of view cv on previous TransitionTemplates.
    *  Called from process. */
  private def effectOfPreviousTransitionTemplates(cv: ComponentView) = {
    val iter = transitionTemplates.iterator(cv.servers)
    while(iter.hasNext){
      val (pre, post, id, e, include) = iter.next
      // assert(pre.servers == cv.servers)
      instantiateTransitionTemplateBy(pre, post, id, e, include, cv)
    }
  }

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) and the view cv.  That is, find each renaming of cv
    * compatible with pre, and that includes a component with identity newPid
    * that optionally can perform oe.  For each, store the transition
    * (extending pre -> post with the transition of the component with
    * identity newPid), the post-state, and calculate the effect on other
    * views.  Called from instantiateTransitionTemplate and
    * effectOfPreviousTransitionTemplates. 
    * @throw FoundErrorException is a concrete transition on error is
    * generated.  */
  @inline private def instantiateTransitionTemplateBy(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean, cv: ComponentView)
  = {
    if(false && verbose) 
      println(s"instantiateTransitionTemplateBy:\n "+
        s"  $pre \n -${system.showEvent(e)}-> $post\n  $cv $newPid")
    Profiler.count("instantiateTransitionTemplateBy")
    require(pre.servers == cv.servers)
    // All states outsideSt that rename a state of cv to give a state with
    // identity newPid, and such that the renaming of cv is consistent with
    // pre; also the next-states of outsideSt after e (if e >= 0).
    val extenders = 
      system.consistentStates(pre, newPid, if(include) e else -1, cv)
    if(false) println(s"extenders = $extenders")
    var i = 0
    while(i < extenders.length){
      val (outsideSt, outsidePosts) = extenders(i); i += 1
      assert(outsidePosts.nonEmpty && 
        outsideSt.componentProcessIdentity == newPid) 
      extendTransitionTemplateBy(pre, post, e, outsideSt, outsidePosts, cv)
    }
  }

  /** Extend the transition template pre -e-> post by adding outsideSt.
    * @param outsidePosts the next state of outsideSt after e
    * @param cv the ComponentView giving the origin of outsideSt.
    * @throw FoundErrorException is a concrete transition on error is
    * generated.*/
  @inline private def extendTransitionTemplateBy(
    pre: Concretization, post: Concretization, e: EventInt, 
    outsideSt: State, outsidePosts: List[State], cv: ComponentView) 
  = {
    if(false && verbose) 
      println(s"extendTransitionTemplateBy($pre, $post, ${system.showEvent(e)},"+
        s" $outsideSt)")
    // Profiler.count("instantiateTT1")
    val referencingViews = extendability.isExtendable(pre, outsideSt)
    if(false) println(s"referencingViews = $referencingViews")
    if(referencingViews != null){
      // Profiler.count("instantiateTT2")
      val extendedPre = pre.extend(outsideSt)
      // Set debugging info
      extendedPre.setSecondaryView(cv, referencingViews, ply) 
      var op = outsidePosts
      while(op.nonEmpty){
        // Profiler.count("instantiateTT3")
        val postSt = op.head; op = op.tail
        val extendedPost = post.extend(postSt)
        // if(verbose && !transitions.contains((extendedPre, e, extendedPost)) &&
        //   !newTransitions.contains((extendedPre, e, extendedPost)))
        // println(s"Extended transition from template $extendedPre\n   -"+
        //   system.showEvent(e)+s"-> $extendedPost")
        if(e == system.Error) throw new FoundErrorException
        // Store this transition, and calculate effect on other views.
        extendedPost.setPly(ply)
        addTransition(extendedPre, e, extendedPost)
      }
    }
  }

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) based on prior views with a renamed version of
    * refState as the principal state.  Called from processTransition.
    * Pre: refState is a component of newPid, with a reference to newPid. */
  private def instantiateTransitionTemplateViaRef(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean, refState: State)
  = { 
    if(verbose) 
      println(s"** instantiateTransitionTemplateViaRef:\n "+
        s"$pre \n  -${system.showEvent(e)}-> $post from $refState")
    Profiler.count("instantiateTransitionTemplateViaRef") // ~60% of TTs
    // Look for views with following as principal
    val princ = Remapper.remapToPrincipal(pre.servers, refState)
    val iter = sysAbsViews.iterator(pre.servers, princ)
    while(iter.hasNext){
      val cv = iter.next
      instantiateTransitionTemplateBy(pre, post, newPid, e, include, cv)
      // IMPROVE: can simplify isExtendable, consistentStates, using the fact
      // that newPid is in position ix.
    }
  }


  // ========= Effect of transitions on other views

  /** Effect on other views of a transition pre -> post.  For every view v1 in
    * sysAbsViews, if it is consistent with pre (i.e. unifiable), and contains
    * at least one process that changes state, then update as per this
    * transition. */
  private 
  def effectOnOthers(pre: Concretization, e: EventInt, post: Concretization) = 
  if(pre != post){
    if(false) println(s"effectOnOthers $pre -${system.showEvent(e)}-> $post")
    // effectOnOthersCount += 1
    val iter = sysAbsViews.iterator(pre.servers)
    while(iter.hasNext){
      val cv = iter.next
      effectOnO.effectOn(pre, e, post, cv, ply, nextNewViews)
    }
  }

  /** The effect of the transition pre -e-> post on cv.  Create extra views
    * caused by the way the transition changes cv. */
  // protected def effectOn(
  //   pre: Concretization, e: EventInt, post: Concretization, cv: ComponentView)
  // = {
  //   assert(false)
  //   // Profiler.count("effectOn")
  //   if(verbose) println(s"effectOn($pre, ${system.showEvent(e)},\n  $post, $cv)")
  //   require(pre.servers == cv.servers && pre.sameComponentPids(post))
  //   val postCpts = post.components; val preCpts = pre.components
  //   // In the case of singleRef, secondary components that might gain a
  //   // reference to c2 = cv.principal (without unification): all pairs (i,id)
  //   // (i >= 1) such that the i'th  component c1 changes state, and id is a
  //   // parameter of c1 in the post state that might reference c2, distinct
  //   // from any component identity in pre, post.  We will subsequently form
  //   // views with c1 as the principal component, referencing c2 (renamed).
  //   val c2Refs = 
  //     if(singleRef) getCrossReferences(preCpts, postCpts, cv.principal.family)
  //     else List[(Int,Identity)]()
  //   // All remappings of cv to unify with pre, together with the list of
  //   // indices of unified components.
  //   val newCpts: ArrayBuffer[(Array[State], List[(Int,Int)])] =
  //     Unification.combine(pre, post, cv, c2Refs.map(_._2)) // IMPROVE 
  //   var cptIx = 0

  //   while(cptIx < newCpts.length){
  //     val (cpts, unifs) = newCpts(cptIx); cptIx += 1
  //     if(debugging){
  //       StateArray.checkDistinct(cpts); assert(cpts.length==cv.components.length)
  //     }
  //     // If singleRef, identities of components referenced by both principals,
  //     // but not included in the views, and such that there is no way of
  //     // instantiating them consistently within sysAbsViews.
  //     val commonMissing: List[ProcessIdentity] = 
  //       if(singleRef && !pre.components.sameElements(cv.components)) 
  //         checkCompatibleMissing(pre.servers, preCpts, cpts)
  //       else List()
  //     // If singleRef and there are references between components from pre and
  //     // cv, then check that that combination is possible in sysAbsViews:
  //     // those that are missing.
  //     val missing: List[ComponentView] =
  //       if(singleRef) missingCrossRefs(pre.servers, cpts, preCpts) else List()
  //     // What does cpts(0) get mapped to?  IMPROVE: we don't need all of unifs
  //     var us = unifs; while(us.nonEmpty && us.head._1 != 0) us = us.tail
  //     val newPrinc = if(us.isEmpty) cpts(0) else postCpts(us.head._2)
  //     var newComponentsList =
  //       StateArray.makePostComponents(newPrinc, postCpts, cpts)
  //     // If singleRef and the secondary component of post has gained a
  //     // reference to newPrinc, we also build views corresponding to those two
  //     // components.
  //     for((i,id) <- c2Refs; if id == newPrinc.ids(0))
  //       newComponentsList ::= Array(postCpts(i), newPrinc)
  //     for(newComponents <- newComponentsList){
  //       val nv = Remapper.mkComponentView(post.servers, newComponents)
  //       newViewCount += 1        // Mostly with unifs.nonEmpty
  //       if(!sysAbsViews.contains(nv)){
  //         if(missing.isEmpty && commonMissing.isEmpty && nextNewViews.add(nv)){
  //           addedViewCount += 1
  //           if(verbose) println(
  //             s"$pre --> $post\n  with unifications $unifs\n"+
  //               s"  induces $cv == ${View.show(pre.servers, cpts)}\n"+
  //               s"  --> ${View.show(post.servers, newComponents)} == $nv")
  //           nv.setCreationInfoIndirect(
  //             pre, cpts, cv, e, post, newComponents, ply)
  //           if(!nv.representableInScript){
  //             println("Not enough identities in script to combine transition\n"+
  //               s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
  //             sys.exit
  //           }
  //         } // end of if(missing.isEmpty && nextNewViews.add(nv))
  //         else if(missing.nonEmpty || commonMissing.nonEmpty){
  //           // Note: we create nv eagerly, even if missing is non-empty: this
  //           // might not be the most efficient approach
  //           val commonMissingTuples = 
  //             commonMissing.map(pid => (pre.servers, preCpts(0), cpts(0), pid))
  //           effectOnStore.add(missing, commonMissingTuples, nv)
  //           if(verbose) println(s"Storing $missing, $commonMissingTuples -> $nv")
  //           nv.setCreationInfoIndirect(
  //             pre, cpts, cv, e, post, newComponents, ply)
  //         }
  //       } // end of if(!sysAbsViews.contains(nv))
  //     } // end of for loop
  //   } // end of while loop
  // }
// IMPROVE: in the calculation of c2Refs, I think we can omit params of
// pre.servers other than cv.principal's identity.
// IMPROVE: could we have more simply achieved the effect of c2Refs by using
// cv with pre.principal as principal, and c2 as secondary component?  This
// assumes pre.principal has a reference to c2, which seems reasonable.

  /** Identify secondary components that can gain a reference to a component of
    * type f.  All pairs (i,id) (with i >= 1) such that the i'th component c1
    * changes state between preCpts and postCpts, and id is a
    * non-distinguished parameter of c1 of family f in the post state, other
    * than an identity in preCpts/postCpts. */
  // @inline private 
  // def getCrossReferences(
  //   preCpts: Array[State], postCpts: Array[State], f: Family)
  //     : List[(Int,Identity)] = {
  //   // Identities in pre: improve
  //   val ids = preCpts.filter(c => c.family == f).map(_.ids(0))
  //   var result = List[(Int,Identity)]() 
  //   for(i <- 1 until preCpts.length; if preCpts(i) != postCpts(i)){
  //     val c1 = postCpts(i); val c1Params = c1.ids
  //     for(j <- 1 until c1Params.length; if c1.typeMap(j) == f){
  //       val p = c1Params(j)
  //       if(!isDistinguished(p) && !ids.contains(p)) result ::= (i, p)
  //     }
  //     }
  //   if(false) println(s"getCrossReferences: $result")
  //   result
  // }

  /** Test whether, if the principal components of cpts1 and cpts2 both have a
    * reference to the same missing component then there is a way of
    * instantiating that component, consistent with the current set of views.
    * @return the identities of all such missing components. */ 
  // private def checkCompatibleMissing(
  //   servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
  //     : List[ProcessIdentity] = {
  //   require(singleRef)
  //   val princ1 = cpts1(0); val princ2 = cpts2(0)
  //   val missingRefs1 = StateArray.missingRefs(cpts1)
  //   val missingRefs2 = StateArray.missingRefs(cpts2)
  //   // The common references considered so far for which there is no way of
  //   // instantiating the referenced component.
  //   var missingCommonRefs = List[ProcessIdentity]()
  //   for(pid <- missingRefs1; if missingRefs2.contains(pid)){
  //     if(!hasCommonRef(servers, princ1, princ2, pid)){
  //       if(verbose){
  //         println(s"checkCompatibleMissing($servers, ${StateArray.show(cpts1)},"+
  //         s" ${StateArray.show(cpts2)})")
  //         println(s"Failed to find states to instantiate common reference $pid")
  //       }
  //       missingCommonRefs ::= pid
  //     }
  //   } // end of for loop
  //   missingCommonRefs
  // }

  /** Is there a component state c with identity pid such that servers || princ1
    * || c and servers || princ2 || c are both in sysAbsViews (up to
    * renaming)? */
  // @inline private def hasCommonRef(
  //   servers: ServerStates, princ1: State, princ2: State, pid: ProcessIdentity)
  //     : Boolean = {
  //   val iter = sysAbsViews.iterator(servers, princ1); var found = false
  //   while(iter.hasNext && !found){
  //     val cv1 = iter.next
  //     val cpt1 = StateArray.find(pid, cv1.components)
  //     if(cpt1 != null){
  //       // println(s"  found $cv1")
  //       // All relevant renamings of cpt1: identity on params of servers and
  //       // princ1, but otherwise either to other params of princ2 or to
  //       // fresh values.
  //       val renames = Unification.remapToJoin(servers, princ1, princ2, cpt1)
  //       for(cv2 <- renames){ // IMPROVE
  //         val cvx = Remapper.mkComponentView(servers, Array(princ2, cv2))
  //         // print(s"  Renamed to $cvx.  ")
  //         if(sysAbsViews.contains(cvx)) found = true
  //         // else println("Not found.")
  //       }
  //     }
  //   } // end of while
  //   found
  // }

  /** Missing cross references, if singleRef.  For each reference from a
    * component c1 of cpts2 to a component c2 of cpts2, or vice versa, test if
    * sysAbsViews contains the view servers || c1 || c2.  Return all such
    * missing views.  */
  // @inline private def missingCrossRefs(
  //   servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
  //     : List[ComponentView] = {
  //   assert(singleRef)
  //   var missing = List[ComponentView]() // missing necessary Views
  //   for(cptsx <- StateArray.crossRefs(cpts1, cpts2)){
  //     val cvx = Remapper.mkComponentView(servers, cptsx)
  //     if(!sysAbsViews.contains(cvx)) missing ::= cvx
  //   }
  //   missing
  // }


  /** The effect of previously found extended transitions on the view cv. */
  private def effectOfPreviousTransitions(cv: ComponentView) = {
    // effectOfPreviousTransitionsCount += 1
    val iter = transitions.iterator(cv.servers)
    while(iter.hasNext){
      val (pre, e, post) = iter.next
      // println(s"considering transition $pre -> $post")
      // effectOnViaTransCount += 1
      effectOnO.effectOn(pre, e, post, cv, ply, nextNewViews)
    }
  }

  /** If cv completes a delayed transition in effectOnStore, then complete it. */
  // private def completeDelayed(cv: ComponentView) = {
  //   assert(false)
  //   for((missing,missingCommon,nv) <- effectOnStore.get(cv)){
  //     // Test if missing and missingCommon now satisfied.
  //     var ok = true; var missing1 = missing
  //     while(ok && missing1.nonEmpty){
  //       val cvx = missing1.head; missing1 = missing1.tail
  //       ok = cvx == cv || sysAbsViews.contains(cvx)
  //     }
  //     var missingCommon1 = missingCommon
  //     while(ok && missingCommon1.nonEmpty){
  //       val (servers, princ1, princ2, pid) = missingCommon1.head
  //       missingCommon1 = missingCommon1.tail
  //       ok = hasCommonRef(servers, princ1, princ2, pid)
  //       if(verbose && ok) 
  //         println(s"${(servers, princ1, princ2, pid)} now satisfied")
  //     }

  //     if(ok && nextNewViews.add(nv)){
  //       val (pre, cpts, cv, post, newComponents) = nv.getCreationIngredients
  //       if(verbose){
  //         println(s"Adding via completeDelayed $cv -> ($missing, $nv)\n"+
  //           s"$pre --> $post\n"+
  //           s"  induces $cv == ${View.show(pre.servers, cpts)}\n"+
  //           s"  --> ${View.show(post.servers, newComponents)} == $nv")
  //       }
  //       if(!nv.representableInScript){
  //         println("Not enough identities in script to combine transition\n"+
  //           s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
  //         sys.exit
  //       }
  //     } // end of outer if
  //   } // end of for loop
  // }

  // ========= Main function

  /** Run the checker. 
    * @param bound the number of plys to explore (with negative values meaning 
    * effectively infinite).  */
  def apply(bound: Int = Int.MaxValue)  = {
    // Get the initial views
    val (sav, initViews) = system.initViews; sysAbsViews = sav
    println("initViews = "+initViews.mkString("; "))
    for(v <- initViews) assert(v.ply == 0)
    var newViews: Array[View] = initViews
    extendability = new Extendability(sysAbsViews)
    effectOnO = new EffectOn(sysAbsViews, system)

    while(!done.get && ply <= bound){
      println("\nSTEP "+ply) 
      println("#abstractions = "+printLong(sysAbsViews.size))
      println(s"#transitions = ${printLong(transitions.size)}")
      println(s"#transition templates = ${printLong(transitionTemplates.size)}")
      println("#new active abstract views = "+printInt(newViews.size))
      nextNewViews = new BasicHashSet[ComponentView]
      newTransitions = new BasicHashSet[Transition]
      newTransitionTemplates = new BasicHashSet[TransitionTemplate]
      var i = 0

      // Process all views from newViews.
      while(i < newViews.length && !done.get){
        if(process(newViews(i))){
          done.set(true)
          val debugger = new Debugger(system, sysAbsViews, initViews)
          debugger(newViews(i))
          ??? // This should be unreachable.
        }
        i += 1
        if(i%50 == 0){ print("."); if(i%500 == 0) print(i) }
      }

      // Add views and transitions found on this ply into the main set.
      println(s"\nCopying: nextNewViews, ${nextNewViews.size}; "+
        s"newTransitions, ${newTransitions.size}; "+
        s"newTransitionTemplates, ${newTransitionTemplates.size}")
      val newViewsAB = new ArrayBuffer[ComponentView]
      def addView(v: ComponentView): Boolean = 
// FIXME: probably not if there's a missing ref. 
        if(sysAbsViews.add(v)){ 
          if(false) println(v)
          assert(v.representableInScript)
          v.ply = ply
          newViewsAB += v; true 
        } 
        else false
      for((pre,e,post) <- newTransitions.iterator){
        assert(transitions.add(pre, e, post))
        // val v = Remapper.remapComponentView(post.toComponentView)
        for(v0 <- post.toComponentView){
          val v = Remapper.remapComponentView(v0)
          if(addView(v)){
            v.setCreationInfo(pre, e, post, ply)
            if(verbose) 
              println(s"$pre -${system.showEvent(e)}->\n  $post gives $v")
          }
        }
      }
      if(false) // print newTransitions
        println(
          (for((pre,e,post) <- newTransitions.iterator.toArray)
          yield s"$pre -${system.showEvent(e)}->\n  $post"
          ).sorted.mkString("\n") )
      for((pre, post, id, e, inc) <- newTransitionTemplates.iterator)
        transitionTemplates.add(pre, post, id, e, inc)
      for(v <- nextNewViews.iterator) addView(v)
      ply += 1; newViews = newViewsAB.toArray; 
      if(verbose) 
        println("newViews =\n"+newViews.map(_.toString).sorted.mkString("\n"))
      if(newViews.isEmpty) done.set(true)
      if(false && ply > 15) println(sysAbsViews.summarise1)
    } // end of main loop

    println("\nSTEP "+ply)
    if(verbose) println(sysAbsViews)
    if(false) println(sysAbsViews.summarise)
    println("#abstractions = "+printLong(sysAbsViews.size))
    println(s"#transitions = ${printLong(transitions.size)}")
    println(s"#transition templates = ${printLong(transitionTemplates.size)}")
    // println(s"effectOnStore size = "+effectOnStore.size)
  }
}






