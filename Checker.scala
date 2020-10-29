package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.ArrayBuffer
import java.util.concurrent.atomic.{AtomicLong,AtomicInteger,AtomicBoolean}

/** A checker for the view abstraction algorithm, applied to system.
  * @param aShapes the shapes of abstractions.
  * @param cShapes the shapes of concretizations. */
class Checker(system: SystemP.System)
{
  /** The abstract views. */
  protected var sysAbsViews: ViewSet = null

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

  /** Add the principal component view of conc to sysAbsViews, and nextNewViews
    * if new. */
  @inline private def addViewFromConc(conc: Concretization) = {
    val v = Remapper.remapComponentView(conc.toComponentView)
    if(addView(v)) println(s"$v.  ***Added***") 
    // else false // println(s"$v.  Already present.")
  }
// FIXME: should we be extracting other views here?

  /** Store the ExtendedTransition pre -> post, and calculate its effect on
    * previously found views. */
  @inline private 
  def addTransition(pre: Concretization, post: Concretization) = {
    transitions.add(pre, post); effectOnOthers(pre, post)
  }

  // ========= Processing a single view

  /** Process v, calculating all the concrete transitions from v, adding the
    * post-states to sysAbsViews, and adding new ones to nextNewViews.
    */
  private def process(v: View) = { 
    println(s"\nProcessing $v")
    v match{
      case cv: ComponentView =>
        for((pre, e, post, outsidePids) <- system.transitions(cv)){ 
          // FIXME: not all transitions included yet
          println(s"\n$pre -${system.showEvent(e)}-> $post ["+
            outsidePids.map(State.showProcessId)+"]")
          assert(pre.components(0) == cv.principal)
          // Find new views as a result of this transition
          processTransition(pre, e, post, outsidePids)
        } // end of for((pre, e, post, outsidePids) <- trans)
        // Effect of previous transitions on this view
        effectOfPreviousTransitions(cv)
        effectOfPreviousTransitionTemplates(cv)
    }
  } 

  // ========= Processing a transition from a view.

  /** Process the transition pre -e-> post, creating the corresponding new views
    * and adding them to sysAbsViews and nextNewViews.  Add appropriate
    * TransitionTemplates and ExtendedTransitions to transitionTemplates and
    * transitions, respectively.
    * @param outsidePids the identities of components outside pre that 
    * synchronise on the transition. */
  @inline private def processTransition(
    pre: Concretization, e: EventInt, post: Concretization, 
    outsidePids: List[ProcessIdentity]) 
  = {
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
      assert(outsidePids.isEmpty) // FIXME (simplifying assumption)
      addViewFromConc(post)
      // Store this transition, and calculate effect on other views.
      addTransition(pre, post)
    }
    else{ // Case 2: one new parameter from outside the view
      assert(newPids.length == 1 && outsidePids.length <= 1)
      // FIXME (simplification)
      val newPid = newPids.head
      // Find all states for newPid, consistent with pre, that can perform e if
      // in outsidePids, and their subsequent states (optionally after e).
      val oe = if(outsidePids.nonEmpty) Some(e) else None
      // Store transition template
      transitionTemplates.add(pre, post, newPid, oe)
      // Get extended transitions based on this
      instantiateTransitionTemplate(pre, post, newPid, oe)
    } // end of else
  }


  // ========= Extending TransitionTemplates 

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, oe) based on prior views.
    * @return all such ExtendedTransitions. 
    * Called from processTransition. */
  private def instantiateTransitionTemplate(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, oe: Option[EventInt]) 
  = {
    val servers = pre.servers
    for(v1 <- sysAbsViews.toArray) v1 match{ // IMPROVE iteration
      case cv: ComponentView =>
        if(cv.servers == servers)
          instantiateTransitionTemplateBy(pre, post, newPid, oe, cv)
    } // end of for ... match
    // result
  }

  /** The effect of view cv on previous TransitionTemplates.
    *  Called from process. */
  private def effectOfPreviousTransitionTemplates(cv: ComponentView) = {
    for((pre, post, id, oe) <- transitionTemplates.iterator){
      if(pre.servers == cv.servers)
        instantiateTransitionTemplateBy(pre, post, id, oe, cv)
    }
  }

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, oe) and the view cv.  For each, store the transition, the
    * post-state, and calculate the effect on other views.
    * Called from instantiateTransitionTemplate and 
    * effectOfPreviousTransitionTemplates. */
  @inline private def instantiateTransitionTemplateBy(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, oe: Option[EventInt], cv: ComponentView)
  = {
    require(pre.servers == cv.servers)
    val extenders = system.consistentStates(newPid, pre, oe, cv)
    for((outsideSt, outsidePosts) <- extenders){
      assert(outsidePosts.nonEmpty)
      if(isExtendable(pre, outsideSt)){
        val extendedPre = pre.extend(outsideSt)
        for(postSt <- outsidePosts){
          val extendedPost = post.extend(postSt)
          println(s"Extended transition from template $extendedPre -"+
            (oe match{ case Some(e) => system.showEvent(e); case None => ""})+
            s"-> $extendedPost")
          addViewFromConc(extendedPost)
          // Store this transition, and calculate effect on other views.
          addTransition(extendedPre, extendedPost)
        }
      }
      else println(s"$outsideSt not compatible with earlier views")
    } // end of for((outsideSt, outsidePosts) <- ...)
  }

  /** Is conc extendable by state st, given the current set of views?  For each
    * component cpt of conc U st, is there a view in SysAbsViews with cpt as
    * the principal component and agreeing on all common processes. 

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

    // FIXME in following: the found view has to be compatible with
    // components, i.e. there has to be a renaming that agrees on any common
    // component.  Test case, the only matching view is aNode(N1,N0) ||
    // bNode(N0,Null) but conc has aNode(N0,Null).
    var found = compatibleWith(servers, components, st)

    if(found){
      // If any component cpt of conc references st, then search for a
      // suitable view with a renaming of cpt and st.  Test case:
      // initNode(T0,N0) || aNode(N0,N1) with st = initNode(N1) should fail,
      // as there's no corresponding view aNode(N0,N1) || initNode(N1).
      val id = st.componentProcessIdentity
      // Test whether any component of conc references st
      var j = 0; val length = components.length
      while(j < length && found){
        val cpt = components(j)
        if(cpt.processIdentities.contains(id)){
          println(s"isExtendable($conc) with reference to $st")
          found = containsXXX(conc, st, j)
        }
        j += 1
      }
    }
    found    
  }

  /** Is st compatible with servers and components given the current views?  Is
    * there a view containing servers, with a renaming of st as principal
    * component, and such that some renaming of the other components agrees
    * with components on common components? */ 
  @inline protected def compatibleWith(servers: ServerStates, components: Array[State], st: State)
      : Boolean = {
    var st1 = Remapper.remapToPrincipal(servers, st) 
    // I think following is incorrect.
    // val id1 = st1.componentProcessIdentity
    // require(components.forall(_.componentProcessIdentity != id1))

    // Test whether there is an existing view with a renaming of st as
    // principal component, and the same servers as conc.  IMPROVE: iteration
    val viewsArray = sysAbsViews.toArray
    var i = 0; var found = false
    while(i < viewsArray.length && !found) viewsArray(i) match{
      case cv1: ComponentView =>
        if(cv1.servers == servers && cv1.principal == st1){
// FIXME: need to check rest of components are compatible.  At present this is
// safe, but maybe giving too many matches.  Gives an extension[12[1](T0,N0)
// || 7[0](N0,N1) || 6[0](N1)] from where initNode.T0.N1.A.N0 performed.
          found = true
        }
        i += 1
    } // end of while ... match

    found
  }


  /** Does sysAbsViews contain a view corresponding to component j's view of
    * conc and st?  Pre: component j references st. */
  private def containsXXX(conc: Concretization, st: State, j : Int): Boolean = {
    println(s"containsXXX($conc, $st, $j)")
    val pCpt = conc.components(j)
    // Rename pCpt to be principal component
    val servers = conc.servers 
    val pCptR = Remapper.remapToPrincipal(servers, pCpt)
    println(s"$pCpt renamed to $pCptR") // TEST: find case where not identity
    // Find index in cpt of reference to st, and hence what st.id gets renamed to
    val stId = st.id
    val k = pCpt.ids.indexOf(stId); assert(k > 0)
    val stIdR = pCptR.ids(k)
    println(s"$st identity renamed to "+State.showProcessId((st.family, stIdR)))
    val cs1 = st.cs    
    
    // Test whether sysAbsViews contains a view matching servers, with cptR as
    // the principal component, and containing a component with identity idR
    // in control state cs1.
    // FIXME: need to check rest also compatible with conc.
    val viewsArray = sysAbsViews.toArray; var i = 0; var found = false
    while(i < viewsArray.length && !found) viewsArray(i) match{
      case cv1: ComponentView =>
        if(cv1.servers == servers && cv1.principal == pCptR &&
          cv1.components.exists(cpt1 => cpt1.cs == cs1 && cpt1.id == stIdR) ){
          println(s"found match with $cv1"); found = true; ???
// FIXME: I'm very unsure about this.
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
  private def effectOnOthers(pre: Concretization, post: Concretization) = {
    // println(s"effectOnOthers($pre, $post)")
    for(v1 <- sysAbsViews.toArray) v1 match{ // IMPROVE iteration
      case cv: ComponentView  =>
        if(cv.servers == pre.servers){
          // println(s"Effect on $cv");
          // IMPROVE if nothing changed state.
          effectOn(pre, post, cv)
        }
    } // end of match
  }
  // IMPROVE: need better way of iterating over ViewSet

  /** The effect of the transition pre -> post on cv.  If cv is consistent with
    * pre (i.e. unifiable), and contains at least one process that changes
    * state, then update as per this transition.  Generate all new views that
    * would result from this view under the transition.  Called by
    * effectOnOthers and effectOfPreviousTransitions.  */
  protected def effectOn(
    pre: Concretization, post: Concretization, cv: ComponentView)
  = {
    // println(s"effectOn($pre, $post, $cv)")
    require(pre.servers == cv.servers)
    val newCpts = Remapper.combine(pre, cv)
    for((cpts, unifs) <- newCpts){
      // println("cpts = "+cpts.mkString("[",",","]")+s"; unifs = $unifs")
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
        else{assert(matches.length == 1); post.components(matches.head._1)}
      val others = newPrinc.processIdentities.tail.
        filter{case(f,id) => !isDistinguished(id)}.map(find(_))
      val nv = Remapper.remapComponentView(
        new ComponentView(post.servers, newPrinc, others) )
      if(addView(nv))
        println(s"Effect of $pre -> $post\n  on $cv:  -> $nv.  ***Added***")
    }
  }

  /** The effect of previously found extended transitions on the view cv. */
  private def effectOfPreviousTransitions(cv: ComponentView) = {
    // println(s"effectOfPreviousTransitions($cv)")
    for((pre,post) <- transitions.iterator){
      // println(s"considering transition $pre -> $post")
      if(pre.servers == cv.servers) effectOn(pre, post, cv)
    }
  }

  // ========= Main function

  /** Run the checker. 
    * @param bound the number of plys to explore (with negative values meaning 
    * effectively infinite).  */
  def apply(bound: Int = Int.MaxValue, verbose: Boolean = false)  = {
    // Get the initial views
    val (sav, initViews) = system.initViews; sysAbsViews = sav
    var newViews: Array[View] = initViews

    while(!done.get && ply <= bound){
      println("\nSTEP "+ply) 
      println("#abstractions = "+printLong(sysAbsViews.size))
      println("#new active abstract views = "+printInt(newViews.size))
      nextNewViews = new ArrayBuffer[View]
      for(v <- newViews) process(v)
      ply += 1; newViews = nextNewViews.toArray; 
      if(newViews.isEmpty) done.set(true)
    }
    println("\nSTEP "+ply)
    println("#abstractions = "+printLong(sysAbsViews.size))
    println(sysAbsViews)
  }


}






