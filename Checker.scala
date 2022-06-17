package ViewAbstraction

import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.Remapper
// import ViewAbstraction.CombinerP.Combiner
// import ViewAbstraction.ExtendabilityP.Extendability
import scala.collection.mutable.{ArrayBuffer,HashSet,HashMap}
import java.util.concurrent.atomic.{AtomicLong,AtomicInteger,AtomicBoolean}

/** A checker for the view abstraction algorithm, applied to system.
  * @param aShapes the shapes of abstractions.
  * @param cShapes the shapes of concretizations. */
class Checker(system: SystemP.System){
  SystemP.System.setSystem(system) // set system in package, for showEvent

  /** The abstract views. */
  protected var sysAbsViews: ViewSet = null
  // Note: reset by CheckerTest

  // Get the initial views, and initialise the view set. 
  val (sav, initViews) = system.initViews; sysAbsViews = sav
  println("initViews = "+initViews.mkString("; "))

  // Note: in various places, we iterate over sysAbsViews.  We should avoid
  // adding new views to the set while that is going on.

  def numViews = sysAbsViews.size

  /** The new views to be considered on the next ply. */
  protected var nextNewViews: MyHashSet[ComponentView] = null

  /** Utility object encapsulating the effectOn and completeDelayed
  * functions. */
  private val effectOn: EffectOn = new EffectOn(sysAbsViews, system)

  val Million = 1000000

  private var done = new AtomicBoolean(false); protected var ply = 1

  /* A Transition is a tuple (pre, e, post): (Concretization, EventInt,
   * Concretization), representing the transition pre -e-> post.  The pre
   * state extends a View by adding all relevant components: components that
   * synchronise on the transition, and any components to which the principal
   * component obtains a reference.*/

  private val transitions = new NewTransitionSet

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

  /** Utility object for extending transition templates. */
  private var transitionTemplateExtender = 
    new TransitionTemplateExtender(transitionTemplates, system, sysAbsViews)

  /** Transition templates found on this ply.  Transition templates are
    * initially added to newTransitionTemplates, but transferred to
    * transitionsTemplates at the end of the ply. */
  private var newTransitionTemplates: MyHashSet[TransitionTemplate] = null

  var addTransitionCount = 0L

  /** Add trans to the set of transitions, and induce new transitions on
    * existing views. */
  private def addTransition(trans: Transition): Unit = {
    // val highlight = 
    //   ComponentView0.highlightServers(pre.servers) && 
    //     pre.servers.servers(5).cs == 152 &&
    //     ComponentView0.highlightServers(post.servers) &&
    //     post.servers.servers(5).cs == 155 &&
    //     pre.components(0).cs == 128 && pre.components(1).cs == 26
    // if(highlight) println(s"\naddTransition($newTrans)")
    addTransitionCount += 1
    if(!transitions.contains(trans)){
      if(newTransitions.add(trans)) effectOnOthers(trans)
      // Note: the views of post get added to sysAbsViews within apply.
    }
  }

  @inline private def addTransitions(buffer: ArrayBuffer[Transition]) =
    for(trans <- buffer) addTransition(trans)


  // ========= Processing a single view

  /** Process cv, calculating all the concrete transitions from cv, adding the
    * post-states to sysAbsViews, and adding new ones to nextNewViews.
    * @return true if a concrete transition on error is generated. 
    */
  private def process(cv: ComponentView): Boolean = { 
    if(verbose) println(s"\n**** Processing $cv")
    if(debugging) StateArray.checkDistinct(cv.components)
    for((pre, e, post, outsidePid) <- system.transitions(cv)){
      if(showTransitions)
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
    // Effect of previous transition templates
    addTransitions(
      transitionTemplateExtender.effectOfPreviousTransitionTemplates(cv) )
    if(singleRef) effectOn.completeDelayed(cv, nextNewViews)
    false
  } 

  // ========= Processing a transition from a view.

  /** Process the transition pre -e-> post, creating the corresponding new views
    * and adding them to sysAbsViews and nextNewViews.  Add appropriate
    * TransitionTemplates and ExtendedTransitions to transitionTemplates and
    * transitions, respectively.
    * @param outsidePid if non-null, the identity of a component outside pre
    * that synchronises on the transition; note, it is assumed that there is
    * at most one.
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
      // Store this transition, and calculate effect on other views.
      addTransition(new Transition(pre, e, post))
    }
    else{ // Case 2: one new parameter from outside the view
      assert(newPids.length == 1) // simplifying assumption
      val newPid = newPids.head
      // Store transition template
      val newTransTemp = (pre, post, newPid, e, outsidePid != null)
      assert(!transitionTemplates.contains(newTransTemp)) // IMPROVE
      newTransitionTemplates.add(newTransTemp)
      // Instantiate the template based on previous views
      addTransitions(
        transitionTemplateExtender.instantiateTransitionTemplate( 
          pre, post, newPid, e, outsidePid != null) )
    } // end of else
  }

  // ========= Effect of transitions on other views

  /** Effect on other views of a transition t.  For every view v1 in
    * sysAbsViews, if it is consistent with t.pre (i.e. unifiable), and
    * contains at least one process that changes state, then update as per
    * this transition. */
  private def effectOnOthers(t: Transition) = if(t.pre != t.post){
    // if(false) println(s"effectOnOthers $t")
    // val highlight = 
    //   ComponentView0.highlightServers(t.preServers) && 
    //     t.pre.components(0).cs == 26 && t.preServers.servers(5).cs == 152
    // if(highlight) println(s"effectOnOthers($t)")
    val iter = 
      if(UseNewViewSet) sysAbsViews.iterator(t)
      else sysAbsViews.iterator(t.preServers)
    while(iter.hasNext){ val cv = iter.next(); effectOn(t, cv, nextNewViews) }
  }

  /** The effect of previously found extended transitions on the view cv. */
  private def effectOfPreviousTransitions(cv: ComponentView) = {
    // val highlight = 
    //   ComponentView0.highlightServers(cv.servers) && 
    //     cv.servers.servers(5).cs == 152 && {
    //     val princ = cv.components(0);
    //     (princ.cs == 45 || princ.cs == 90 || princ.cs == 91) 
    //   } && {
    //     val second = cv.components(1);
    //     second.cs == 11 && second.ids(1) == 4 && second.ids(2) == 5
    //   }
    // if(highlight) println(s"\neffectOfPreviousTransitions($cv)")
    val iter = transitions.iterator(cv)//.toArray
    while(iter.hasNext){ 
      val t = iter.next()
      // Note: second clause is because another transition in the same batch
      // might have succeeded.
/*
      assert(t.mightGiveSufficientUnifs(cv) || 
          cv.containsDoneInduced(t.post.servers),
        s"t = $t;\n cv = $cv\n"+cv.containsDoneInduced(t.post.servers))
 */
      effectOn(t, cv, nextNewViews)
    }
  }

  // ========= Main function

  /** Run the checker. 
    * @param bound the number of plys to explore (with negative values meaning 
    * effectively infinite).  */
  def apply(bound: Int = Int.MaxValue)  = {
    var newViews: Array[ComponentView] = initViews

    while(!done.get && ply <= bound){
      println("\nSTEP "+ply) 
      println("#abstractions = "+printLong(sysAbsViews.size))
      // println(s"#transitionsX = ${printLong(transitionsX.size)}")
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
        if(i%200 == 0){ print("."); if(i%2000 == 0) print(i) }
      }

      // Add views and transitions found on this ply into the main set.
      println(s"\nCopying: nextNewViews, ${nextNewViews.size}; "+
        s"newTransitions, ${newTransitions.size}; "+
        s"newTransitionTemplates, ${newTransitionTemplates.size}")
      val newViewsAB = new ArrayBuffer[ComponentView]
      /* Add v to sysAbsViews and newViewsAB if new.  Return true if so. */
      def addView(v: ComponentView): Boolean = {
        if(sysAbsViews.add(v)){ 
          assert(v.representableInScript); newViewsAB += v; true 
        } 
        else false
      } // end of addView
      // Now transitions
      for(t <- newTransitions.iterator){
        assert(transitions.add(t))
        for(v0 <- t.post.toComponentView){
          val v = Remapper.remapComponentView(v0)
          if(addView(v)){
            v.setCreationInfo(t.pre, t.e, t.post) 
            if(showTransitions /* || ComponentView0.highlight(v) */) 
              println(s"${t.toString}\ngives $v")
          }
        }
      }
      // Store transition templates
      for((pre, post, id, e, inc) <- newTransitionTemplates.iterator)
        transitionTemplates.add(pre, post, id, e, inc)
      // Strore new views
      for(v <- nextNewViews.iterator){
        addView(v)
        // if(showTransitions){
        //   println(s"adding $v from nextNewViews")
        //   if(findTarget(v)){
        //     println("***")
        //     val (pre, cpts, cv, post, newComponents) = v.getCreationIngredients
        //     println(s"Adding  $cv -> $v\n"+
        //       s"$pre --> $post\n"+
        //       s"  induces $cv == ${View.show(pre.servers, cpts)}\n"+
        //       s"  --> ${View.show(post.servers, newComponents)} == $v")
        //   }
        // }
      }
      ply += 1; newViews = newViewsAB.toArray; 
      if(showEachPly)
        println("newViews =\n"+newViews.map(_.toString).sorted.mkString("\n"))
      if(newViews.isEmpty) done.set(true)
    } // end of main loop

    println("\nSTEP "+ply+"\n")
    if(singleRef && doSanityCheck && bound == Int.MaxValue) effectOn.sanityCheck
    // Following is expensive: IMPROVE: enable via switch
    if(singleRef && reportEffectOn) effectOn.report
    if(showViews) println(sysAbsViews)
    //if(false) println(sysAbsViews.summarise)
    println("#abstractions = "+printLong(sysAbsViews.size))
    // println(s"#transitionsX = ${printLong(transitionsX.size)}")
    println(s"#transitions = ${printLong(transitions.size)}")
    println(s"#transition templates = ${printLong(transitionTemplates.size)}")
    println(s"#ServerStates = ${ServerStates.count}")
    println(s"#States = ${MyStateMap.stateCount}")
    
    // println(s"effectOnStore size = "+effectOnStore.size)
  }

  import ox.gavin.profiling.MemoryProfiler.traverse  

  /** Perform a memory profile of this. */
  def memoryProfile = {
    println("Memory profile"); println()

    println("# states = "+MyStateMap.stateCount)
    traverse("MyStateMap", MyStateMap, maxPrint = 0); println()

    traverse("ServerStates", ServerStates, maxPrint = 0); println()

    traverse("first view", sysAbsViews.iterator.next(), maxPrint = 0); println()

    traverse("sysAbsViews", sysAbsViews, maxPrint = 0); println()

    traverse("transitions", transitions, maxPrint = 0); println()

    traverse("transitionTemplates", transitionTemplates, maxPrint = 0); println()

    // traverse("extendability", extendability, maxPrint = 0); println()
    traverse("transitionTemplateExtender", transitionTemplateExtender, 
      maxPrint = 0)
    println()

    if(true){
      traverse("system", system, maxPrint = 0); println() }
    else println("Omitting system\n") 

    //traverse("effectOn", effectOn, maxPrint = 5, maxPrintArray = 8); println
    effectOn.memoryProfile; println()

    traverse("checker", this, maxPrint = 0); println()
  }
}






