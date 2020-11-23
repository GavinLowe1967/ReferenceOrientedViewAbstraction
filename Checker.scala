package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.ArrayBuffer
import java.util.concurrent.atomic.{AtomicLong,AtomicInteger,AtomicBoolean}

/** A checker for the view abstraction algorithm, applied to system.
  * @param aShapes the shapes of abstractions.
  * @param cShapes the shapes of concretizations. */
class Checker(system: SystemP.System){
  private var verbose = true 

  private var veryVerbose = false

  /** The abstract views. */
  protected var sysAbsViews: ViewSet = null

  private def showTransition(
    pre: Concretization, e: EventInt, post: Concretization) =
    s"$pre -${system.showEvent(e)}-> $post"
  val Million = 1000000

  private var done = new AtomicBoolean(false); private var ply = 1

  /** The new views to be considered on the next ply. */
  protected var nextNewViews: ArrayBuffer[View] = null

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
  @inline private def addView(v: View): Boolean = {
    if(sysAbsViews.add(v)){ nextNewViews += v; true }
    else false
  }

  /** Add the principal component view of pre to sysAbsViews, and nextNewViews
    * if new, based on the extended transition pre -e-> post. */
  @inline private 
  def addViewFromConc(pre: Concretization, e: EventInt, post: Concretization) = {
    val v = Remapper.remapComponentView(post.toComponentView)
    if(addView(v)){
      if(verbose) println(s"$v.  ***Added***") 
      // from ${showTransition(pre,e,post)}
      v.setCreationInfo(pre, e, post)
    }
    // else false // println(s"$v.  Already present.")
  }

  /** Store the ExtendedTransition pre -> post, and calculate its effect on
    * previously found views. */
  @inline private 
  def addTransition(pre: Concretization, e: EventInt, post: Concretization) = {
    transitions.add(pre, e, post); effectOnOthers(pre, e, post)
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
        for((pre, e, post, outsidePids) <- system.transitions(cv)){ 
          // FIXME: not all transitions included yet
          if(verbose)
            println(s"\n$pre -${system.showEvent(e)}-> $post ["+
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
      addViewFromConc(pre, e, post)
      // Store this transition, and calculate effect on other views.
      addTransition(pre, e, post)
    }
    else{ // Case 2: one new parameter from outside the view
      assert(newPids.length == 1 && outsidePids.length <= 1)
      // IMPROVE (simplification)
      val newPid = newPids.head
      // Find all states for newPid, consistent with pre, that can perform e if
      // in outsidePids, and their subsequent states (optionally after e).
      //val oe = if(outsidePids.nonEmpty) Some(e) else None
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
        for(postSt <- outsidePosts){
          val extendedPost = post.extend(postSt)
          if(verbose)
            println(s"Extended transition from template $extendedPre -"+
              system.showEvent(e)+s"-> $extendedPost")
          assert(e != system.Error) // FIXME
          addViewFromConc(extendedPre, e, extendedPost) // FIXME
          // Store this transition, and calculate effect on other views.
          addTransition(extendedPre, e, extendedPost)
        }
      }
      else if(verbose) println(s"$outsideSt not compatible with earlier views")
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
    // Also every other state in conc is compatible FIXME CHECK
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

  /** Is st compatible with servers and components given the current views?
    * Does some renaming of an existing view match servers, have st as
    * principal component, and agree with components on common components?
    * Equivalently, is there a view containing servers, with a renaming of st
    * as principal component, and such that some renaming of the other
    * components agrees with components on common components? */ 
  @inline protected def compatibleWith(
    servers: ServerStates, components: Array[State], st: State)
      : Boolean = {
    // Remap st so it can be the principal component with servers.
    val map = Remapper.createMap(servers.rhoS)
    val nextArgs = Remapper.createNextArgMap(servers.rhoS)
    var st1 = Remapper.remapState(map, nextArgs, st)
    // IMPROVE: compare with Remapper.remapToPrincipal(servers, st)

    val otherArgs = Remapper.newOtherArgMap
    // Create map as identity function on server ids and mapping st1 back to
    // st.  This is the base of the renaming applied to a view in sysAbsViews,
    // to try to produce a view that matches servers, has st as principal
    // component, and agrees with components on common components
    val map1 = Remapper.createMap(servers.rhoS)
    for(j <- 0 until st1.ids.length){
      val id = st1.ids(j); if(id >= 0) map1(st1.typeMap(j))(id) = st.ids(j)
    }
// FIXME: I think otherArgs should include ids of components that are not in 

    // Test whether there is an existing view with a renaming of st as
    // principal component, and the same servers as conc.  IMPROVE: iteration
    val viewsArray = sysAbsViews.toArray
    var i = 0; var found = false
    // println(st1)
    while(i < viewsArray.length && !found) viewsArray(i) match{
      case cv1: ComponentView =>
        if(cv1.servers == servers && cv1.principal == st1){
          // Test if a renaming of cv1.components that matches st also agrees
          // with components on common components.
          found = Remapper.areUnifiable(
            cv1.components, components, map1, 0, otherArgs)
        }
        i += 1
    } // end of while ... match

    found
  }

  /** Does sysAbsViews contain a view with conc.servers, conc.components(j) as
    * principal component, and including a renaming of st?  FIXME: should also
    * include any other component of conc referenced by conc.components(j).
    * 
    * Pre: component j references st.
    * Test case: conc.components = initNodeSt(T0,N0) || aNode(N0,N1), st =
    * initNode(N1), would need a view aNode(N0,N1) || initNode(N1). */
  protected[Checker] 
  def containsReferencingView(conc: Concretization, st: State, j : Int)
      : Boolean = {
    if(veryVerbose) println(s"containsReferencingView($conc, $st, $j)")
    val servers = conc.servers; val pCpt = conc.components(j); val stId = st.id
    // Rename pCpt to be principal component
    val map = Remapper.createMap(servers.rhoS)
    val nextArgs = Remapper.createNextArgMap(servers.rhoS)
    val pCptR = Remapper.remapState(map, nextArgs, pCpt)
    // Remapper.remapToPrincipal(servers, pCpt)
    if(veryVerbose || pCpt != pCptR)
      println(s"$pCpt renamed to $pCptR") // TEST: find case where not identity
    // what st.id gets renamed to
    val stIdR = map(st.family)(stId)
    // Following fails if pCpt does not reference st, i.e. precondition false.
    assert({val ix = pCpt.ids.indexOf(stId); ix >= 0 && pCptR.ids(ix) == stIdR}, 
      s"pCptR = $pCptR; st = $st")
    if(veryVerbose) 
      println(s"$st identity renamed to "+
        State.showProcessId((st.family, stIdR)))
    val cs1 = st.cs    
    
    // Test whether sysAbsViews contains a view matching servers, with cptR as
    // the principal component, and containing a component with identity idR
    // in control state cs1.
    // FIXME: need to check rest also compatible with conc.
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
              if(Remapper.unify(map, cpt1, st)) found = true
              else if(verbose) println(s"failed to unify $cpt1 and $st") 
            }
            j += 1
          }
          if(found && verbose) println(s"found match with $cv1")
// FIXME: check remainder of conc consistent with cv1.
// NOTE: need to clone map.
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
    // println(s"effectOnOthers($pre, $post)")
    for(v1 <- sysAbsViews.toArray) v1 match{ // IMPROVE iteration
      case cv: ComponentView  =>
        if(cv.servers == pre.servers){
          // println(s"Effect on $cv");
          // IMPROVE if nothing changed state.
          effectOn(pre, e, post, cv)
        }
    } // end of match
  }
  // IMPROVE: need better way of iterating over ViewSet

  /** The effect of the transition pre -e-> post on cv.  If cv is consistent with
    * pre (i.e. unifiable), and contains at least one process that changes
    * state, then update as per this transition.  Generate all new views that
    * would result from this view under the transition.  Called by
    * effectOnOthers and effectOfPreviousTransitions.  */
  protected def effectOn(
    pre: Concretization, e: EventInt, post: Concretization, cv: ComponentView)
  = {
    // println(s"effectOn($pre, $post, $cv)")
    require(pre.servers == cv.servers)
    val newCpts = Remapper.combine(pre, cv)
    for((cpts, unifs) <- newCpts){
      // println("cpts = "+cpts.mkString("[",",","]")+s"; unifs = $unifs")
      // pre U cpts is a consistent view.  
      // pre.components(i) = cpts(j)  iff  (i,j) in unifs

      // Find the component of cpts with process identity pid, or return
      // null if no such.
      def find0(pid: ProcessIdentity, cpts: Array[State]): State = {
        var i = 0; var done = false
        while(i < cpts.length && !done){
          if(cpts(i).componentProcessIdentity == pid) done = true else i += 1
        }
        if(done) cpts(i) else null
      }
      // Find the component of post or cpts with process identity pid
      def find(pid: ProcessIdentity): State = {
        val st1 = find0(pid, post.components)
        if(st1 != null) st1
        else{
          val st2 = find0(pid, cpts)
          assert(st2 != null, s"Not found identity $pid in $post or "+
            cpts.mkString("[",",","]"))
          st2
        }
      }
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
      val others = newPrinc.processIdentities.tail.
        filter{case(f,id) => !isDistinguished(id)}.map(find(_))
      val nv = Remapper.remapComponentView(
        new ComponentView(post.servers, newPrinc, others) )
      if(addView(nv)){
        val extendedPre = new Concretization(pre.servers, 
            View.union(pre.components, cpts))
        val extendedPost = new Concretization(post.servers, 
          View.union(post.components, newPrinc +: others))
        if(verbose)
          println(s"Effect of "+showTransition(pre,e,post)+
            // "\n"+showTransition(extendedPre, e, extendedPost)+
            s" on $cv:  -> $nv.  ***Added***")
        nv.setCreationInfo(extendedPre, e, extendedPost)
      }
    }
  }

  /** The effect of previously found extended transitions on the view cv. */
  private def effectOfPreviousTransitions(cv: ComponentView) = {
    // println(s"effectOfPreviousTransitions($cv)")
    for((pre, e, post) <- transitions.iterator){
      // println(s"considering transition $pre -> $post")
      if(pre.servers == cv.servers) effectOn(pre, e, post, cv) // FIXME
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
    var newViews: Array[View] = initViews.filter(system.isActive)

    while(!done.get && ply <= bound){
      println("\nSTEP "+ply) 
      println("#abstractions = "+printLong(sysAbsViews.size))
      println("#new active abstract views = "+printInt(newViews.size))
      nextNewViews = new ArrayBuffer[View]
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
      // for(v <- newViews) assert(! process(v))
      ply += 1; newViews = nextNewViews.toArray; 
      if(newViews.isEmpty) done.set(true)
    }
    println("\nSTEP "+ply)
    println(sysAbsViews)
    println("#abstractions = "+printLong(sysAbsViews.size))
  }


}






