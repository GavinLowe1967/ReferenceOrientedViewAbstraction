package ViewAbstraction

import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.{Remapper,Unification}
import ViewAbstraction.CombinerP.Combiner
import scala.collection.mutable.{ArrayBuffer,HashSet,HashMap}
import java.util.concurrent.atomic.{AtomicLong,AtomicInteger,AtomicBoolean}

/** A checker for the view abstraction algorithm, applied to system.
  * @param aShapes the shapes of abstractions.
  * @param cShapes the shapes of concretizations. */
class Checker(system: SystemP.System){
  private var verbose = false 
  private var veryVerbose = false

  /** The abstract views. */
  protected var sysAbsViews: ViewSet = null
  // Note: in various places, we iterate over sysAbsViews.  We should avoid
  // adding new views to the set while that is going on.

  /** The new views to be considered on the next ply. */
  protected var nextNewViews: HashSet[ComponentView] = null

  private def showTransition(
    pre: Concretization, e: EventInt, post: Concretization) =
    s"$pre -${system.showEvent(e)}-> $post"

  val Million = 1000000

  private var done = new AtomicBoolean(false); private var ply = 1

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
  private var newTransitions: HashSet[Transition] = null

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
  private var newTransitionTemplates: HashSet[TransitionTemplate] = null


  var addTransitionCount = 0L
  // var effectOnCount = 0
  // var effectOnViaOthersCount = 0
  // var effectOnViaTransCount = 0
  var effectOfPreviousTransitionsCount = 0
  var effectOnOthersCount = 0
  var newViewCount = 0L
  var addedViewCount = 0L
  var effectOnRepetition = 0
  var instantiateTransitionTemplateCount = 0L
  // Counts on transition templates


  /** Store the ExtendedTransition pre -> post, and calculate its effect on
    * previously found views. */
  @inline private 
  def addTransition(pre: Concretization, e: EventInt, post: Concretization)
  = {
    addTransitionCount += 1
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
    v match{
      case cv: ComponentView =>
        for((pre, e, post, outsidePid) <- system.transitions(cv)){ 
          if(verbose)
            println(s"$pre -${system.showEvent(e)}-> $post ["+
              (if(outsidePid != null) State.showProcessId(outsidePid) else "")+
              "]")
          assert(pre.components(0) == cv.principal)
          // Find new views as a result of this transition
          if(processTransition(pre, e, post, outsidePid)){
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
    * @param outsidePid if non-null, the identity of a component outside pre
    * that synchronises on the transition.  // FIXME: At most one?
    * @return true if a concrete transition on error is generated. */
  @inline private def processTransition(
    pre: Concretization, e: EventInt, post: Concretization, 
    outsidePid: ProcessIdentity)
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
    assert(newPids.length <= 1) // simplifying assumption
    // The following assertion (outsidePid in newPids) captures an assumption
    // that the principal component cannot acquire a reference from nowhere:
    // the reference must be acquired either from another process in the view
    // or by synchronising with that other component.
    if(outsidePid != null) assert(newPids.head == outsidePid)

    if(newPids.isEmpty){
      // Case 1: no new nondistinguished parameter
      if(e == system.Error) return true
      // if(!newVersion) addViewFromConc(pre, e, post)
      // Store this transition, and calculate effect on other views.
      addTransition(pre, e, post)
    }
    else{ // Case 2: one new parameter from outside the view
      // assert(newPids.length == 1) // simplifying assumption
      val newPid = newPids.head
      // Store transition template
      val newTransTemp = (pre, post, newPid, e, outsidePid != null)
      assert(!transitionTemplates.contains(newTransTemp)) // IMPROVE
      newTransitionTemplates.add(newTransTemp)
      // Counting of different types of TransitionTemplates; IMPROVE
      if(outsidePid != null){
        // println("Sync: "+system.showEvent(e))
        Profiler.count("TransitionTemplate sync")
      }
      else if(pre.components.exists(_.processIdentities.contains(newPid))){
        // println("From component: "+system.showEvent(e))
        Profiler.count("TransitionTemplate component")
      }
      else{
        // println("From server: "+system.showEvent(e))
        assert(pre.servers.servers.exists(_.processIdentities.contains(newPid)),
          s"pre = $pre; newPid = $newPid")
        Profiler.count("TransitionTemplate server")
      }
      // Get extended transitions based on this
      instantiateTransitionTemplate(pre, post, newPid, e, outsidePid != null)
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
    instantiateTransitionTemplateCount += 1
    sysAbsViews.iterator(pre.servers).foreach{ cv =>
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
// Principal component? 
    * that optionally can perform oe.  For each, store the transition
    * (extending pre -> post with the transition of the component with
    * identity newPid), the post-state, and calculate the effect on other
    * views.  Called from instantiateTransitionTemplate and
    * effectOfPreviousTransitionTemplates. */
  @inline private def instantiateTransitionTemplateBy(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean, cv: ComponentView)
  = {
    Profiler.count("instantiateTransitionTemplateBy")
    require(pre.servers == cv.servers)
    if(false) println(s"instantiateTransitionTemplateBy($pre,\n"+
        s"  ..., ${system.showEvent(e)}+, ..., $cv)")
    val extenders = 
      system.consistentStates(pre, newPid, if(include) e else -1, cv)
    for((outsideSt, outsidePosts) <- extenders){
      assert(outsidePosts.nonEmpty)
      Profiler.count("instantiateTT1")
// Following is bottleneck
      if(isExtendable(pre, outsideSt)){
        Profiler.count("instantiateTT2")
        val extendedPre = pre.extend(outsideSt)
        extendedPre.setSecondaryView(cv) // for debugging purposes
        var op = outsidePosts
        while(op.nonEmpty){
          val postSt = op.head; op = op.tail
          val extendedPost = post.extend(postSt)
          if(verbose && !transitions.contains((extendedPre, e, extendedPost)) && 
            !newTransitions.contains((extendedPre, e, extendedPost)))
            println(s"Extended transition from template $extendedPre\n   -"+
              system.showEvent(e)+s"-> $extendedPost")
          assert(e != system.Error) // FIXME 
          // Store this transition, and calculate effect on other views.
          addTransition(extendedPre, e, extendedPost)
        }
      }
      else if(veryVerbose) 
        println(s"$outsideSt not compatible with earlier views")
    } // end of for((outsideSt, outsidePosts) <- ...)
  }

  /** A cache of results of previous calls to isExtendable.  If a value isn't in
    * the mapping, then that indicates that compatibleWith previously gave
    * only false.  A result of k >= 0 indicates that compatibleWith gave true,
    * and that calls to containsReferencingView gave true for all relevant j
    * in [0..k). */
  private val isExtendableCache = new HashMap[(Concretization, State), Int]

  /** Is pre extendable by state st, given the current set of views?  For each
    * component cpt of pre U st, is there a view in SysAbsViews with cpt as
    * the principal component and agreeing on all common processes (up to
    * renaming).
    * 
    * PRE: pre is compatible with SysAbsViews, and pre does not include
    * st.identity.  This means it is enough to check the condition for cpt =
    * st or a non-principal component of pre that references st. ??????
    */
  @inline protected 
  def isExtendable(pre: Concretization, st: State): Boolean = {
    require(sysAbsViews.contains(pre.toComponentView))
    // Also every other state in conc is compatible FIXME CHECK ???
    require(pre.components.forall(
      _.componentProcessIdentity != st.componentProcessIdentity))
    val servers = pre.servers; val components = pre.components
    val k = isExtendableCache.getOrElse((pre, st), -1)
    Profiler.count("isExtendable"+k)

    // Does SysAbsViews contain a view consistent with pre and with a
    // renaming of st as principal component?
    var found = k >= 0 || compatibleWith(pre, st)

    if(found){
      // If any component cpt of pre references st, then search for a
      // suitable view with a renaming of cpt and st. 
      val id = st.componentProcessIdentity
      // Test whether any component of pre references st
      var j = k max 0; val length = components.length
// IMPROVE: does this always hold for j = 0, i.e. is this a preconditon? 
      while(j < length && found){
        if(components(j).processIdentities.contains(id)){
          if(veryVerbose) println(s"isExtendable($pre) with reference to $st")
          found = containsReferencingView(pre, st, j)
        }
        j += 1
      }
      isExtendableCache += (pre,st) -> (if(found) j else j-1)
    }
    found    
  }

  /** Cached results of calls to Combiner.areUnifiable.  Effectively a map
    * (List[State], List[List[Identity]], List[List[Identity]]) =>
    *  Array[State] => Boolean.   */
  private val compatibleWithCache = new CompatibleWithCache

  /** Is `st` compatible with `pre` given the current views?  Does some renaming
    * of an existing view match `pre.servers`, have `st` as principal
    * component, and agree with `pre.components` on common components?
    * Equivalently, is there a view containing `pre.servers`, with a renaming
    * of `st` as principal component, and such that some renaming of the other
    * components agrees with `pre.components` on common components? */ 
  @inline protected 
  def compatibleWith(pre: Concretization, st: State): Boolean = {
    val servers = pre.servers; val components = pre.components
    // Remap st so it can be the principal component with servers.
    val map = servers.remappingMap; val nextArgs = servers.nextArgMap
    var st1 = Remapper.remapState(map, nextArgs, st)
    // IMPROVE: compare with Remapper.remapToPrincipal(servers, st)

    val otherArgs = Remapper.newOtherArgMap
    // Create map as identity function on `server` ids and mapping `st1` back
    // to `st`.  This is the base of the renaming applied to a view in
    // `sysAbsViews`, to try to produce a view that matches `servers`, has
    // `st` as principal component, and agrees with `components` on common
    // components
    val map1 = servers.remappingMap; val typeMap = st1.typeMap
    val ids1 = st1.ids; var j = 0
    while(j < ids1.length){
      val id = ids1(j)
      if(id >= 0){ 
        val id1 = map1(typeMap(j))(id); assert(id1 < 0 || id1 == st.ids(j))
        map1(typeMap(j))(id) = st.ids(j)
      }
      j += 1
    }

    // Get cache corresponding to components, map1 and otherArgs.
    val cache = compatibleWithCache.get( 
      (pre.componentsList, map1.map(_.toList).toList, otherArgs.toList)) 
    // Test whether there is an existing view with a renaming of st as
    // principal component, and the same servers as conc.  
    var found = false; val iter = sysAbsViews.iterator(servers, st1)
    while(iter.hasNext && !found){
      val cv1 = iter.next; assert(cv1.principal == st1)
      // Does a renaming of the other components of cv1 (consistent with
      // servers and st1) also agree with components on common components?
      // Try to get cached result.
      val cpts1 = cv1.components // List
      cache.get(cpts1) match{
        case Some(b) => // Profiler.count("compatibleWith"+b); 
          found = b
        case None =>
          Profiler.count("compatibleWith-null")
          found =
            Combiner.areUnifiable(cv1.components, components, map1, 0, otherArgs)
          cache.add(cpts1,found)
      } // end of match
    } // end of while ... match
    // Profiler.count("compatibleWith"+found)  
    found
  }

  /** Does `sysAbsViews` contain a view with `pre.servers`,
    * `pre.components(j)` as principal component, and including a renaming of
    * `st`?  FIXME: should also include any other component of `pre`
    * referenced by `pre.components(j)`.
    * 
    * Pre: `pre.components(j)` references `st`.
    * Test case: pre.components = initNodeSt(T0,N0) || aNode(N0,N1), st =
    * initNode(N1), would need a view aNode(N0,N1) || initNode(N1). */
  protected[Checker] 
  def containsReferencingView(pre: Concretization, st: State, j : Int)
      : Boolean = {
    if(veryVerbose) println(s"containsReferencingView($pre, $st, $j)")
    val servers = pre.servers; val pCpt = pre.components(j)
    assert(pCpt.processIdentities.contains(st.componentProcessIdentity))//precond
    // Rename pCpt to be principal component
    val map = servers.remappingMap; val nextArgs = servers.nextArgMap
    val pCptR = Remapper.remapState(map, nextArgs, pCpt)
    // st.id gets renamed to stIdR
    val (stF, stId) = st.componentProcessIdentity; val stIdR = map(stF)(stId)
    // Check pCpt references st, i.e.  precondition.
    assert(pCptR.processIdentities.contains((stF,stIdR)))
    val cs1 = st.cs    
    // Find other components of pre that are referenced by pCpt
    val pLen = pCpt.ids.length; val pRefs = new Array[State](pLen)
    val pIds = pCpt.processIdentities
    for(i <- 0 until pre.components.length; if i != j){
      val cpt = pre.components(i); var ix = 0
      // Find index of cpt.componentProcessIdentity in pIds 
      while(ix < pLen && pIds(ix) != cpt.componentProcessIdentity) ix += 1
      assert(ix != 0)
      if(ix < pLen) pRefs(ix) = cpt
    }

    // Test whether sysAbsViews contains a view cv1 matching servers, with
    // cptR as the principal component, and containing a component with
    // identity idR in control state cs1.  map (and map1) tries to map pre
    // onto cv1.  
    val iter = sysAbsViews.iterator(servers, pCptR); var found = false
    while(iter.hasNext && !found){
      val cv1 = iter.next; assert(cv1.principal == pCptR); var j = 1
      // Test if cv1 contains a component that is a renaming of st under
      // an extension of map
      while(j < cv1.components.length && !found){
        val cpt1 = cv1.components(j)
        if(cpt1.cs == cs1 && cpt1.id == stIdR){
          // test if cpt1 is a renaming of st under an extension of map
          var map2 = Unification.unify(map, cpt1, st)
          if(map2 != null){
            // Check that all components referenced by pCpt in pre are matched
            // by a corresponding component in cv1.  map2 != null if true for
            // all components so far.
            var k = 1
            while(k < pRefs.length && map2 != null){
              if(pRefs(k) != null)
                map2 = Unification.unify(map2, cv1.components(k), pRefs(k))
              k += 1
            } // end of inner while
            found = map2 != null
          } // end of if(map2 != null)
        }
        j += 1
      }
      if(found && veryVerbose) println(s"found match with $cv1")
    } // end of while(iter.hasNext && !found)
    found
  }


  // ========= Effect of transitions on other views

  /** Effect on other views of a transition pre -> post.  For every view v1 in
    * sysAbsViews, if it is consistent with pre (i.e. unifiable), and contains
    * at least one process that changes state, then update as per this
    * transition. */
  private 
  def effectOnOthers(pre: Concretization, e: EventInt, post: Concretization) = 
  if(pre != post){
    // effectOnOthersCount += 1
    val iter = sysAbsViews.iterator(pre.servers)
    while(iter.hasNext){
      val cv = iter.next
      // IMPROVE if nothing changed state.
      // effectOnViaOthersCount += 1
      effectOn(pre, e, post, cv)
    }
  }


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
    // effectOnCount += 1
    // if(veryVerbose) 
    //   println(s"effectOn($pre, ${system.showEvent(e)},\n  $post, $cv)")
    require(pre.servers == cv.servers &&
      pre.components.length == post.components.length)
    val changedServers = pre.servers != post.servers
    // View.checkDistinct(cv.components)
    // All ways of merging cv and pre
    val newCpts: ArrayBuffer[(Array[State], Unification.Unifications)] = 
      if(changedServers) Unification.combine(pre, cv)
      else{
        // Only look for cases where a component of cv unifies with a
        // component of pre that changes state.
        val preC = pre.components; val postC = post.components
        val flags = new Array[Boolean](preC.length); var i = 0
        while(i < preC.length){ flags(i) = preC(i) != postC(i); i += 1 }
        // val flags = Array.tabulate(preC.length)(i => preC(i) != postC(i))
        Unification.combineWithUnification(pre, flags, cv)
    }
    var cptIx = 0
    while(cptIx < newCpts.length){
      val (cpts, unifs) = newCpts(cptIx); cptIx += 1
      assert(changedServers || unifs.nonEmpty)
      // View.checkDistinct(cpts)
      // pre U cpts is a consistent view.  
      // pre.components(i) = cpts(j)  iff  (i,j) in unifs.
      // Find what cpts(0) gets mapped to by unifs
      var us = unifs
      while(us.nonEmpty && us.head._2 != 0) us = us.tail
      val newPrinc =
        if(us.isEmpty) cpts(0)
        else{
          val ix = us.head._1           
          // assert(cpts(0) == pre.components(ix), 
          //   s"${cpts(0)}, ${pre.components(ix)}")
          post.components(ix)
        }
      var others = new ArrayBuffer[State]; val len = newPrinc.ids.length
      val pids = newPrinc.processIdentities
      var i = 1; val princId = newPrinc.componentProcessIdentity // pids(0)
      while(i < len){
        val pid = pids(i) // newPrinc.processIdentity(i) // pids(i)
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
              // assert(st2 != null, s"Not found identity $pid in $post or "+
              //   cpts.mkString("[",",","]"))
              others += st2
            }
          }
        }
        i += 1
      }
      val othersA = others.toArray
      // View.checkDistinct(others, newPrinc.toString)
      val nv = Remapper.mkComponentView(post.servers, newPrinc, othersA)
      // View.checkDistinct(nv.components, View.showStates(others))
      newViewCount += 1
      if(!nv.representableInScript){
        println("Not enough identities in script to combine transition\n"+
          s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
        sys.exit
      }
      if(!sysAbsViews.contains(nv)){ // TODO: test if this helps
        nextNewViews += nv; addedViewCount += 1
        val extendedPre = new Concretization(pre.servers, 
            View.union(pre.components, cpts))
        extendedPre.setSecondaryView(cv) 
        val extendedPost = new Concretization(post.servers, 
          View.union(post.components, newPrinc +: othersA))
        nv.setCreationInfo(extendedPre, e, extendedPost)
      }
    }
  }

  /** The effect of previously found extended transitions on the view cv. */
  private def effectOfPreviousTransitions(cv: ComponentView) = {
    // effectOfPreviousTransitionsCount += 1
    val iter = transitions.iterator(cv.servers)
    while(iter.hasNext){
      val (pre, e, post) = iter.next
      // println(s"considering transition $pre -> $post")
      // assert(pre.servers == cv.servers)
      // effectOnViaTransCount += 1
      effectOn(pre, e, post, cv)
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
      println(s"#transitions = ${printLong(transitions.size)}")
      println(s"#transition templates = ${printLong(transitionTemplates.size)}")
      println("#new active abstract views = "+printInt(newViews.size))
      nextNewViews = new HashSet[ComponentView]
      newTransitions = new HashSet[Transition]
      newTransitionTemplates = new HashSet[TransitionTemplate]
      var i = 0

      // Process all views from newViews.
      while(i < newViews.length && !done.get){
        if(process(newViews(i))){
          done.set(true)
          val debugger = new Debugger(system, sysAbsViews, initViews)
          debugger(newViews(i))
          ??? 
        }
        i += 1
        if(i%20 == 0){ print("."); if(i%500 == 0) print(i) }
      }

      // Add views and transitions found on this ply into the main set.
      println(s"\nCopying: nextNewViews, ${nextNewViews.size}; "+
        s"newTransitions, ${newTransitions.size}; "+
        s"newTransitionTemplates, ${newTransitionTemplates.size}")
      val newViewsAB = new ArrayBuffer[ComponentView]
      def addView(v: ComponentView): Boolean = 
        if(sysAbsViews.add(v)){ 
          if(false) println(v)
          newViewsAB += v; true 
        } 
        else false
      for((pre,e,post) <- newTransitions){
        assert(transitions.add(pre, e, post)) // IMPROVE: assert this worked
        val v = Remapper.remapComponentView(post.toComponentView)
        if(addView(v)) v.setCreationInfo(pre, e, post)
      }
      if(false) // print newTransitions
        println(
          (for((pre,e,post) <- newTransitions.toArray)
          yield s"$pre -${system.showEvent(e)}->\n  $post"
          ).sorted.mkString("\n") )
      for((pre, post, id, e, inc) <- newTransitionTemplates)
        transitionTemplates.add(pre, post, id, e, inc)
      for(v <- nextNewViews) addView(v)
      ply += 1; newViews = newViewsAB.toArray; 
      if(false) 
        println("newViews =\n"+newViews.map(_.toString).sorted.mkString("\n"))
      if(newViews.isEmpty) done.set(true)
    } // end of main loop

    println("\nSTEP "+ply)
    if(verbose) println(sysAbsViews)
    println("#abstractions = "+printLong(sysAbsViews.size))
  }


}






