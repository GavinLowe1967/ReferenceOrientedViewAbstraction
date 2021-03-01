package ViewAbstraction

import ViewAbstraction.RemapperP.{Remapper,Unification}
import ViewAbstraction.CombinerP.Combiner
import scala.collection.mutable.ArrayBuffer
import java.util.concurrent.atomic.{AtomicLong,AtomicInteger,AtomicBoolean}

/** A checker for the view abstraction algorithm, applied to system.
  * @param aShapes the shapes of abstractions.
  * @param cShapes the shapes of concretizations. */
class Checker(system: SystemP.System){
  // Are we adding views, etc. only at the end of plys? 
  // private var newVersion = true // FIXME: remove

  private var verbose = false 
  private var veryVerbose = false

  /** The abstract views. */
  protected var sysAbsViews: ViewSet = null
  // Note: in various places, we iterate over sysAbsViews.  We should avoid
  // adding new views to the set while that is going on.

  /** The new views to be considered on the next ply. */
  //protected var nextNewViews: ArrayBuffer[View] = null

  private var nextNewViews1: ArrayBuffer[View] = null

// FIXME: don't need both

  private def showTransition(
    pre: Concretization, e: EventInt, post: Concretization) =
    s"$pre -${system.showEvent(e)}-> $post"

  val Million = 1000000

  private var done = new AtomicBoolean(false); private var ply = 1

  /** An extended transition represents the pre- and post-states of a
    * transition, and extends a View by adding in the states of any additional
    * components that synchronise on the transition, and any components to
    * which the principal component obtains a reference. */
  private type ExtendedTransition = (Concretization, Concretization)

  /** The extended transitions found so far.  Abstractly, a set of
    * ExtendedTransitions. */
  private val transitions: TransitionSet = new SimpleTransitionSet

  /** A TransitionTemplate (pre, post, id, oe) represents an extended transition
    * pre U st --> post U st' for every state st and st' such that (1) st and
    * st' have identity id; (2) st is compatible with pre; (3) if oe = Some(e)
    * then st -e-> st', otherwise st = st'.  */
  private type TransitionTemplate = TransitionTemplateSet.TransitionTemplate
  // (Concretization, Concretization, ProcessIdentity, Option[EventInt])

  private val transitionTemplates: TransitionTemplateSet = 
    new SimpleTransitionTemplateSet

  /** Add v to  sysAbsViews, and nextNewViews if new. */
  // @inline private def addView(v: View): Boolean = {
  //   View.checkDistinct(v.asInstanceOf[ComponentView].components)
  //   if(sysAbsViews.add(v)){ 
  //     if(verbose) println(s"$v.  ***Added***") 
  //     nextNewViews += v; true 
  //   }
  //   else false
  // }

  // /** Add the principal component view of pre to sysAbsViews, and nextNewViews
  //   * if new, based on the extended transition pre -e-> post. 
  //   * 
  //   * Note: this is called only at the end of each ply, to avoid adding to
  //   * sysAbsViews while iterating over it.*/
  // @inline private 
  // def addViewFromConc(pre: Concretization, e: EventInt, post: Concretization) = {
  //   val v = Remapper.remapComponentView(post.toComponentView)
  //   if(addView(v)){
  //     if(verbose) println(s"  from ${showTransition(pre,e,post)}")
  //     v.setCreationInfo(pre, e, post)
  //   }
  // }

  private var newTransitions
      : ArrayBuffer[(Concretization, EventInt, Concretization)] = null

  /** Store the ExtendedTransition pre -> post, and calculate its effect on
    * previously found views. */
  @inline private 
  def addTransition(pre: Concretization, e: EventInt, post: Concretization) = {
    newTransitions += ((pre, e, post))
    transitions.add(pre, e, post); effectOnOthers(pre, e, post)
  }


  // private def addView1(v: ComponentView, pre: Concretization, cpts: Array[State],
  //   post: Concretization, e: EventInt, cv: ComponentView) 
  // = {
  //     if(addView(v)){
  //       addedViewCount += 1
  //       val extendedPre = new Concretization(pre.servers, 
  //           View.union(pre.components, cpts))
  //       extendedPre.setSecondaryView(cv) 
  //       val extendedPost = new Concretization(post.servers, 
  //         View.union(post.components, v.components)) // newPrinc +: othersA))
  //       v.setCreationInfo(extendedPre, e, extendedPost)
  //     }
  // }


  // ========= Processing a single view

  /** Process v, calculating all the concrete transitions from v, adding the
    * post-states to sysAbsViews, and adding new ones to nextNewViews.
    * @return true if a concrete transition on error is generated. 
    */
  private def process(v: View): Boolean = { 
    if(verbose) println(s"\n**** Processing $v")
    v match{
      case cv: ComponentView =>
        for((pre, e, post, outsidePids) <- system.transitions(cv)){ 
          if(verbose)
            println(s"$pre -${system.showEvent(e)}-> $post ["+
              outsidePids.map(State.showProcessId)+"]")
          assert(pre.components(0) == cv.principal)
          // Find new views as a result of this transition
          if(processTransition(pre, e, post, outsidePids)){
            assert(e == system.Error); return true
          }
        } // end of for((pre, e, post, outsidePids) <- trans)
        // Effect of previous transitions on this view
        effectOfPreviousTransitions(cv)
        effectOfPreviousTransitionTemplates(cv)
    }
    false
  } 

  // ========= Processing a transition from a view.

  /** Process the transition pre -e-> post, creating the corresponding new views
    * and adding them to sysAbsViews and nextNewViews.  Add appropriate
    * TransitionTemplates and ExtendedTransitions to transitionTemplates and
    * transitions, respectively.
    * @param outsidePids the identities of components outside pre that 
    * synchronise on the transition. 
    * @return true if a concrete transition on error is generated. */
  @inline private def processTransition(
    pre: Concretization, e: EventInt, post: Concretization, 
    outsidePids: List[ProcessIdentity])
      : Boolean = {
    val princ1 = post.components(0)
    // Process ids of other components
    val otherIds = pre.components.tail.map(_.componentProcessIdentity)
    assert(post.components.map(_.componentProcessIdentity).sameElements(
      pre.components.map(_.componentProcessIdentity)))
    // newPids is the components to which the principal component gains
    // references but that are outside pre/post.
    val newPids: Array[ProcessIdentity] =
      princ1.processIdentities.tail.filter(p =>
        !isDistinguished(p._2) && !otherIds.contains(p))
    // The following assertion (outsidePids subset of newPids) captures an
    // assumption that the principal component cannot acquire a reference from
    // nowhere: the reference must be acquired either from another process in
    // the view or by synchronising with that other component.
    assert(outsidePids.forall(pid => newPids.contains(pid)))
    // if(newPids.nonEmpty)
    //   println(s"newPids = "+newPids.map(State.showProcessId).mkString(","))

    if(newPids.isEmpty){
      // Case 1: no new nondistinguished parameter
      assert(outsidePids.isEmpty) // IMPROVE (simplifying assumption)
      if(e == system.Error) return true
      // if(!newVersion) addViewFromConc(pre, e, post)
      // Store this transition, and calculate effect on other views.
      addTransition(pre, e, post)
    }
    else{ // Case 2: one new parameter from outside the view
      assert(newPids.length == 1 && outsidePids.length <= 1)
      // IMPROVE (simplification)
      val newPid = newPids.head
      // Store transition template
      transitionTemplates.add(pre, post, newPid, e, outsidePids.nonEmpty)
      // Get extended transitions based on this
      instantiateTransitionTemplate(pre, post, newPid, e, outsidePids.nonEmpty)
    } // end of else
    false
  }


  // ========= Extending TransitionTemplates 

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) based on prior views.
    * @return all such ExtendedTransitions. 
    * Called from processTransition. */
  private def instantiateTransitionTemplate(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean) 
  = {
    val servers = pre.servers
    for(v1 <- sysAbsViews.toArray) v1 match{ // IMPROVE iteration
      case cv: ComponentView =>
        if(cv.servers == servers)
          instantiateTransitionTemplateBy(pre, post, newPid, e, include, cv)
    } // end of for ... match
    // result
  }

  /** The effect of view cv on previous TransitionTemplates.
    *  Called from process. */
  private def effectOfPreviousTransitionTemplates(cv: ComponentView) = {
    for((pre, post, id, e, include) <- transitionTemplates.iterator){
      if(pre.servers == cv.servers)
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
    * effectOfPreviousTransitionTemplates. */
  @inline private def instantiateTransitionTemplateBy(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean, cv: ComponentView)
  = {
    require(pre.servers == cv.servers)
    val extenders = // IMPROVE: avoid Option value
      system.consistentStates(newPid, pre, if(include) Some(e) else None, cv)
    for((outsideSt, outsidePosts) <- extenders){
      assert(outsidePosts.nonEmpty)
      if(isExtendable(pre, outsideSt)){
        val extendedPre = pre.extend(outsideSt)
        extendedPre.setSecondaryView(cv) // for debugging purposes
        for(postSt <- outsidePosts){
          val extendedPost = post.extend(postSt)
          if(verbose)
            println(s"Extended transition from template $extendedPre -"+
              system.showEvent(e)+s"-> $extendedPost")
          assert(e != system.Error) // FIXME
          // if(!newVersion) addViewFromConc(extendedPre, e, extendedPost) 
          // Store this transition, and calculate effect on other views.
          addTransition(extendedPre, e, extendedPost)
        }
      }
      else if(veryVerbose) 
        println(s"$outsideSt not compatible with earlier views")
    } // end of for((outsideSt, outsidePosts) <- ...)
  }

  /** Is conc extendable by state st, given the current set of views?  For each
    * component cpt of conc U st, is there a view in SysAbsViews with cpt as
    * the principal component and agreeing on all common processes (up to
    * renaming).
    * 
    * PRE: conc is compatible with SysAbsViews, and conc does not include
    * st.identity.  This means it is enough to check the condition for cpt =
    * st or a non-principal component of conc that references st. ??????
    */
  @inline protected 
  def isExtendable(conc: Concretization, st: State): Boolean = {
    require(sysAbsViews.contains(conc.toComponentView))
    // Also every other state in conc is compatible FIXME CHECK ???
    require(conc.components.forall(
      _.componentProcessIdentity != st.componentProcessIdentity))
    val servers = conc.servers; val components = conc.components

    // Does SysAbsViews contain a view consistent with conc and with a
    // renaming of st as principal component?
    var found = compatibleWith(servers, components, st)

    if(found){
      // If any component cpt of conc references st, then search for a
      // suitable view with a renaming of cpt and st. 
      val id = st.componentProcessIdentity
      // Test whether any component of conc references st
      var j = 0; val length = components.length
      while(j < length && found){
        if(components(j).processIdentities.contains(id)){
          if(veryVerbose) println(s"isExtendable($conc) with reference to $st")
          found = containsReferencingView(conc, st, j)
        }
        j += 1
      }
    }
    found    
  }

  /** Is `st` compatible with `servers` and `components` given the current
    * views?  Does some renaming of an existing view match `servers`, have
    * `st` as principal component, and agree with `components` on common
    * components?  Equivalently, is there a view containing `servers`, with a
    * renaming of `st` as principal component, and such that some renaming of
    * the other components agrees with `components` on common components? */ 
  @inline protected def compatibleWith(
    servers: ServerStates, components: Array[State], st: State)
      : Boolean = {
    // Remap st so it can be the principal component with servers.
    val map = Remapper.createMap(servers.rhoS)
    val nextArgs = Remapper.createNextArgMap(servers.rhoS)
    var st1 = Remapper.remapState(map, nextArgs, st)
    // IMPROVE: compare with Remapper.remapToPrincipal(servers, st)

    val otherArgs = Remapper.newOtherArgMap
    // Create map as identity function on `server` ids and mapping `st1` back
    // to `st`.  This is the base of the renaming applied to a view in
    // `sysAbsViews`, to try to produce a view that matches `servers`, has
    // `st` as principal component, and agrees with `components` on common
    // components
    val map1 = Remapper.createMap(servers.rhoS); val typeMap = st1.typeMap
    for(j <- 0 until st1.ids.length){
      val id = st1.ids(j); 
      if(id >= 0){ 
        assert{val id1 = map1(typeMap(j))(id); id1 < 0 || id1 == st.ids(j)}
        map1(typeMap(j))(id) = st.ids(j)
      }
    }

    // Test whether there is an existing view with a renaming of st as
    // principal component, and the same servers as conc.  IMPROVE: iteration
    val viewsArray = sysAbsViews.toArray
    var i = 0; var found = false
    // println(st1)
    while(i < viewsArray.length && !found) viewsArray(i) match{
      case cv1: ComponentView =>
        if(cv1.servers == servers && cv1.principal == st1){
          // Does a renaming of the other components of cv1 (consistent with
          // servers and st1) also agree with components on common components?
          found = Combiner.areUnifiable(
            cv1.components, components, map1, 0, otherArgs)
          // IMPROVE: use cv1.others here? 
        }
        i += 1
    } // end of while ... match

    found
  }

  /** Does `sysAbsViews` contain a view with `conc.servers`,
    * `conc.components(j)` as principal component, and including a renaming of
    * `st`?  FIXME: should also include any other component of `conc`
    * referenced by `conc.components(j)`.
    * 
    * Pre: `conc.components(j)` references `st`.
    * Test case: conc.components = initNodeSt(T0,N0) || aNode(N0,N1), st =
    * initNode(N1), would need a view aNode(N0,N1) || initNode(N1). */
  protected[Checker] 
  def containsReferencingView(conc: Concretization, st: State, j : Int)
      : Boolean = {
    if(veryVerbose) println(s"containsReferencingView($conc, $st, $j)")
    val servers = conc.servers; val pCpt = conc.components(j)
    val (stF, stId) = st.componentProcessIdentity
    // Rename pCpt to be principal component
    val map = Remapper.createMap(servers.rhoS)
    val nextArgs = Remapper.createNextArgMap(servers.rhoS)
    val pCptR = Remapper.remapState(map, nextArgs, pCpt)
    // Remapper.remapToPrincipal(servers, pCpt) - IMPROVE?
    if(veryVerbose /* || pCpt != pCptR */) println(s"$pCpt renamed to $pCptR")
    // what st.id gets renamed to
    val stIdR = map(stF)(stId)
    // Following fails if pCpt does not reference st, i.e. precondition false.
    assert({ val ix = pCpt.processIdentities.indexOf((stF,stId)); 
      ix >= 0 && pCptR.ids(ix) == stIdR},
      s"pCptR = $pCptR; st = $st")
    if(veryVerbose) 
      println(s"$st identity renamed to "+
        State.showProcessId((st.family, stIdR)))
    val cs1 = st.cs    
    // Find other components of conc that are referenced by pCpt
    val pRefs = new Array[State](pCpt.ids.length)
    for(i <- 0 until conc.components.length; if i != j){
      val cpt = conc.components(i)
      val ix = pCpt.processIdentities.indexOf(cpt.componentProcessIdentity)
      if(ix >= 0){ assert(ix != 0); pRefs(ix) = cpt } 
    }
    // println(s"pRefs = "+pRefs.mkString("; "))

    // Test whether sysAbsViews contains a view cv1 matching servers, with
    // cptR as the principal component, and containing a component with
    // identity idR in control state cs1.  map (and map1) tries to map conc
    // onto cv1.  
    val viewsArray = sysAbsViews.toArray; var i = 0; var found = false
    while(i < viewsArray.length && !found) viewsArray(i) match{
      case cv1: ComponentView =>
        if(cv1.servers == servers && cv1.principal == pCptR){
          // Test if cv1 contains a component that is a renaming of st under
          // an extension of map
          var j = 1
          while(j < cv1.components.length && !found){
            val cpt1 = cv1.components(j)
            if(cpt1.cs == cs1 && cpt1.id == stIdR){
              // test if cpt1 is a renaming of st under an extension of map
              var map2 = Unification.unify(map, cpt1, st)
              if(map2 != null){
                // Check that all components referenced by pCpt in conc are
                // matched by a corresponding component in cv1.  map2 != null
                // if true for all components so far.
                var k = 1
                while(k < pRefs.length && map2 != null){
                  if(pRefs(k) != null){
                    map2 = Unification.unify(map2, cv1.components(k), pRefs(k))
                    if(veryVerbose)
                      println(s"Trying to unify ${cv1.components(k)} and "+
                        pRefs(k)+".  "+(if(found) "Succeeded." else "Failed."))
                  }
                  k += 1
                } // end of inner while
                found = map2 != null
              } // end of if(map2 != null)
              else if(veryVerbose) println(s"failed to unify $cpt1 and $st") 
            }
            j += 1
          }
          if(found && veryVerbose) println(s"found match with $cv1")
          // else println(s"did not  match with $cv1")
        }
        i += 1
    }
    found
  }


  // ========= Effect of transitions on other views

  /** Effect on other views of a transition pre -> post.  For every view v1 in
    * sysAbsViews, if it is consistent with pre (i.e. unifiable), and contains
    * at least one process that changes state, then update as per this
    * transition. */
  private 
  def effectOnOthers(pre: Concretization, e: EventInt, post: Concretization) = {
    effectOnOthersCount += 1
    // println(s"effectOnOthers($pre, $post)")
    val vs = sysAbsViews.toArray; var i = 0
    while(i < vs.length){
      vs(i) match{ // IMPROVE iteration
        case cv: ComponentView  =>
          View.checkDistinct(cv.components)
          if(cv.servers == pre.servers){
            // println(s"Effect on $cv");
            // IMPROVE if nothing changed state.
            effectOnViaOthersCount += 1
            effectOn(pre, e, post, cv)
          }
      } // end of match
      i += 1
    }
  }
  // IMPROVE: need better way of iterating over ViewSet

  var effectOnCount = 0
  var effectOnViaOthersCount = 0
  var effectOnViaTransCount = 0
  var effectOfPreviousTransitionsCount = 0
  var effectOnOthersCount = 0
  var newViewCount = 0L
  var addedViewCount = 0L
  var changedServersCount = 0L
  var effectOnRepetition = 0

  /** Find the component of cpts with process identity pid, or return null if no
    * such.  IMPROVE: move elsewhere, combine with Unification.find */
  @inline private def find0(pid: ProcessIdentity, cpts: Array[State]): State = {
    var i = 0
    while(i < cpts.length && cpts(i).componentProcessIdentity != pid)
      i += 1
    if(i < cpts.length) cpts(i) else null
  }

  /** Show the result of a call to Unifications.combine. */
  private def showUnifs(
      us: ArrayBuffer[(Array[State], Unification.Unifications)]) =
    us.map{ case(sts,us) => "("+View.showStates(sts)+", "+us+")" }.mkString("; ")

  /** The effect of the transition pre -e-> post on cv.  If cv is consistent with
    * pre (i.e. unifiable), and contains at least one process that changes
    * state, then update as per this transition.  Generate all new views that
    * would result from this view under the transition.  Called by
    * effectOnOthers and effectOfPreviousTransitions.  */
  protected def effectOn(
    pre: Concretization, e: EventInt, post: Concretization, cv: ComponentView)
  = {
    effectOnCount += 1
    if(veryVerbose) 
      println(s"effectOn($pre, ${system.showEvent(e)},\n  $post, $cv)")
    require(pre.servers == cv.servers &&
      pre.components.length == post.components.length)
    val changedServers = pre.servers != post.servers
    if(changedServers) changedServersCount += 1
    // Check elements of cv.components are distinct
    View.checkDistinct(cv.components)
    // All ways of merging cv and pre
    val newCpts = 
      if(changedServers) Unification.combine(pre, cv)
      else{
        // Only look for cases where a component of cv unifies with a
        // component of pre that changes state.
        val preC = pre.components; val postC = post.components
        val flags = Array.tabulate(preC.length)(i => preC(i) != postC(i))
        val newCpts2 = Unification.combineWithUnification(pre, flags, cv)
        if(false){
          // Compare with newCptsX; find those elements of newCpts such that at
          // last one component of pre that changes is unified.
          val newCptsX = Unification.combine(pre, cv)
          val newCptsF =
            newCptsX.filter{ case(_,u) =>
              u.filter{ case(k,j) => flags(k) }.nonEmpty }
          assert(// newCptsF.length == newCpts2.length &&
            newCptsF.forall{case(sts,us) => newCpts2.exists{case(sts1,us1) =>
              sts.sameElements(sts1) && us==us1}} &&
              newCpts2.forall{case(sts,us) => newCptsF.exists{case(sts1,us1) =>
                sts.sameElements(sts1) && us==us1}},
            "newCptsX = "+showUnifs(newCptsX)+"\n"+
              "newCpts2 = "+showUnifs(newCpts2))
        }
        newCpts2
    }
    // Do we have repetitions?  We might. 
    // val hasReps = !newCpts.forall{ case(sts,unifs) =>
    //   newCpts.forall{ case(sts1,unifs1) =>
    //     sts == sts1 || unifs != unifs1 || !sts.sameElements(sts1) } }
    // // Check newCpts is distinct
    // if(hasReps) effectOnRepetition += 1
    // assert(true || !hasReps,
    //   s"changedServers = $changedServers\npre = $pre\ncv = $cv"+
    //     "\nnewCpts = "+showUnifs(newCpts))
    for((cpts, unifs) <- newCpts){
      assert(changedServers || unifs.nonEmpty)
      View.checkDistinct(cpts)
      // pre U cpts is a consistent view.  
      // pre.components(i) = cpts(j)  iff  (i,j) in unifs.
      // Find what cpts(0) gets mapped to by unifs
      val matches = unifs.filter(_._2 == 0)
      val newPrinc =
        if(matches.isEmpty) cpts(0)
        else{
          assert(matches.length == 1)
          assert(cpts(0) == pre.components(matches.head._1), 
            s"${cpts(0)}, ${pre.components(matches.head._1)}")
          post.components(matches.head._1)
        }
      // Find other processes referenced by newPrinc
      // val others = newPrinc.processIdentities.tail.distinct.
      //   filter{case(f,id) => !isDistinguished(id)}.map(find(_))
      var others = new ArrayBuffer[State]; val len = newPrinc.ids.length
      // var k = 0 // # entries in others
      val pids = newPrinc.processIdentities
      var i = 1; val princId = newPrinc.componentProcessIdentity // pids(0)
      while(i < len){
        val pid = newPrinc.processIdentity(i) // pids(i)
        if(!isDistinguished(pid._2) && pid != princId){
          // check this is first occurrence of pid
          var j = 1; while(j < i && pids(j) != pid) j += 1
          if(j == i){
            // Find the component of post or cpts with process identity pid, 
            // and add to others
            val st1 = find0(pid, post.components)
            if(st1 != null) others += st1
            else{
              val st2 = find0(pid, cpts)
              assert(st2 != null, s"Not found identity $pid in $post or "+
                cpts.mkString("[",",","]"))
              others += st2
            }
          }
        }
        i += 1
      }
      val othersA = others.toArray
      // View.checkDistinct(others, newPrinc.toString)
      val nv = Remapper.remapComponentView(
        new ComponentView(post.servers, newPrinc, othersA) )
      // View.checkDistinct(nv.components, View.showStates(others))
      newViewCount += 1
      // Common code in the new and old versions, below
      def common = { // IMPROVE: unfactor
        assert(pre.servers != post.servers || unifs.nonEmpty)// IMPROVE?
        addedViewCount += 1
        // if(verbose) 
        //   println(s" from effectOn($pre, ${system.showEvent(e)}, $post, $cv)")
        val extendedPre = new Concretization(pre.servers, 
            View.union(pre.components, cpts))
        extendedPre.setSecondaryView(cv) 
        val extendedPost = new Concretization(post.servers, 
          View.union(post.components, newPrinc +: othersA))
        if(veryVerbose)
          println(s"Effect of "+showTransition(pre,e,post)+
            // "\n"+showTransition(extendedPre, e, extendedPost)+
            s" on $cv:  -> $nv.  ***Added***")
        nv.setCreationInfo(extendedPre, e, extendedPost)
      }
      // if(newVersion){
      if(!sysAbsViews.contains(nv)){ // TODO: test if this helps
        nextNewViews1 += nv; common
      }
      // }
      // else if(addView(nv)) common
    }
  }

  /** The effect of previously found extended transitions on the view cv. */
  private def effectOfPreviousTransitions(cv: ComponentView) = {
    effectOfPreviousTransitionsCount += 1
    // println(s"effectOfPreviousTransitions($cv)")
    for((pre, e, post) <- transitions.iterator){
      // println(s"considering transition $pre -> $post")
      if(pre.servers == cv.servers){
        effectOnViaTransCount += 1
        effectOn(pre, e, post, cv)
      }
    }
  }

  // ========= Main function

  /** Run the checker. 
    * @param bound the number of plys to explore (with negative values meaning 
    * effectively infinite).  */
  def apply(bound: Int = Int.MaxValue)  = {
    // Get the initial views
    val (sav, initViews) = system.initViews; sysAbsViews = sav
    println("initViews = "+initViews.mkString("; "))
    var newViews: Array[View] = initViews // .filter(system.isActive)

    while(!done.get && ply <= bound){
      println("\nSTEP "+ply) 
      println("#abstractions = "+printLong(sysAbsViews.size))
      println("#new active abstract views = "+printInt(newViews.size))
      // nextNewViews = new ArrayBuffer[View]; 
      nextNewViews1 = new ArrayBuffer[View]
      newTransitions = 
        new ArrayBuffer[(Concretization, EventInt, Concretization)]
      var i = 0
      while(i < newViews.length && !done.get){
        if(process(newViews(i))){
          done.set(true)
          val debugger = new Debugger(system, sysAbsViews, initViews)
          debugger(newViews(i))
          ??? 
        }
        i += 1
      }
      //if(newVersion){
        // Add views found on this ply into the main set. 
      val nextNewViews = new ArrayBuffer[View]
      def addView(v: View): Boolean = 
        if(sysAbsViews.add(v)){ nextNewViews += v; true } else false
      for((pre,e,post) <- newTransitions){
        val v = Remapper.remapComponentView(post.toComponentView)
        if(addView(v)) v.setCreationInfo(pre, e, post)
      }
      for(v <- nextNewViews1) addView(v)
      //}
      ply += 1; newViews = nextNewViews.toArray; 
      if(newViews.isEmpty) done.set(true)
    }
    println("\nSTEP "+ply)
    if(true || verbose) println(sysAbsViews)
    println("#abstractions = "+printLong(sysAbsViews.size))
  }


}






