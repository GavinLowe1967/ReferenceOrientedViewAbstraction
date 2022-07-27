package ViewAbstraction

import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer,HashSet,HashMap}
import java.util.concurrent.atomic.{AtomicLong,AtomicInteger,AtomicBoolean}

/** A checker for the view abstraction algorithm, applied to system.
  * @param numWorkers the number of concurrent workers to run. */
class Checker(system: SystemP.System, numWorkers: Int){

  // Get the initial views, and initialise the view set. 
  private val (sav, initViews) = system.initViews 
  println("initViews = "+initViews.mkString("; "))

  /** The abstract views. */
  protected var sysAbsViews: ViewSet = sav 
  // Note: reset by CheckerTest

  /** The new views to be considered on the next ply. */
  protected var nextNewViews: MyHashSet[ComponentView] = null

  /* The transitions found so far. */
  private val transitions = new NewTransitionSet

  /** Transitions found on this ply.  Transitions are initially added to
    * newTransitions, but transferred to transitions at the end of the ply. */
  private var newTransitions: BasicHashSet[Transition] = null

  /** The transition templates found on previous plies.  Abstractly, a set of
    * TransitionTemplates. */
  private val transitionTemplates: TransitionTemplateSet = 
    new ServerBasedTransitionTemplateSet

  /** Transition templates found on this ply.  Transition templates are
    * initially added to newTransitionTemplates, but transferred to
    * transitionsTemplates at the end of the ply. */
  private var newTransitionTemplates: MyHashSet[TransitionTemplate] = null

  /* Note: in various places, we iterate over sysAbsViews, transitions and
   * transitionTemplates.  We avoid adding new elements to these sets while
   * that is going on.  Instead, elements are added to nextNewViews,
   * newTransitions and newTransitionTemplates, and added to the main sets at
   * the end of each ply. */

  def numViews = sysAbsViews.size

  /* Initialise utility object encapsulating the effectOn and completeDelayed
   * functions. */
  EffectOn.init(sysAbsViews, system)

  /** Utility object for extending transition templates. */
  private val transitionTemplateExtender = 
    new TransitionTemplateExtender(transitionTemplates, system, sysAbsViews)

  var addTransitionCount = 0L

  /** Add trans to the set of transitions, and induce new transitions on
    * existing views. */
  private def addTransition(trans: Transition): Unit = {
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
    if(processViewTransitions(cv)) return true
    // Effect of previous transitions on this view
    effectOfPreviousTransitions(cv)
    // Effect of previous transition templates
    addTransitions(
      transitionTemplateExtender.effectOfPreviousTransitionTemplates(cv) )
    if(singleRef) EffectOn.completeDelayed(cv, nextNewViews)
    false
  } 

  /** Process the view transitions from cv.  
    * @return true if a concrete transition on error is generated. 
    */
  @inline private def processViewTransitions(cv: ComponentView): Boolean = {
    if(verbose) println(s"\n**** Processing $cv")
    if(debugging) StateArray.checkDistinct(cv.components)
    for((pre, e, post, outsidePid) <- system.transitions(cv)){
      if(showTransitions)
        println(s"$pre -${showEvent(e)}-> $post ["+
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
      println(s"processTransition:\n  $pre -${showEvent(e)}-> $post"+
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
      s"$pre -${showEvent(e)}-> $post:\n"+
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
      val newTransTemp =
        new TransitionTemplate(pre, post, newPid, e, outsidePid != null)
      if(debugging) assert(!transitionTemplates.contains(newTransTemp)) 
      newTransitionTemplates.add(newTransTemp)
      // Instantiate the template based on previous views
      addTransitions(
        transitionTemplateExtender.instantiateTransitionTemplate(newTransTemp) )
    } // end of else
  }

  // ========= Effect of transitions on other views

  /** Effect on other views of a transition t.  For every view v1 in
    * sysAbsViews, if it is consistent with t.pre (i.e. unifiable), and
    * contains at least one process that changes state, then update as per
    * this transition. */
  private def effectOnOthers(t: Transition) = if(t.pre != t.post){
    val iter = 
      if(UseNewViewSet) sysAbsViews.iterator(t)
      else sysAbsViews.iterator(t.preServers)
    while(iter.hasNext){ 
      val cv = iter.next(); new EffectOn(t, cv, nextNewViews)() 
    }
  }

  /** The effect of previously found extended transitions on the view cv. */
  private def effectOfPreviousTransitions(cv: ComponentView) = {
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
      new EffectOn(t, cv, nextNewViews)()
    }
  }

  // Extending transition templates

  /** Try instantiating previous transition templates with view. */
  @inline private def instantiateTransitiontemplates(view: ComponentView) =
    addTransitions(
      transitionTemplateExtender.effectOfPreviousTransitionTemplates(view) )

  // ========= Main function

  /** The views to be expanded on the current ply. */
  private var newViews: Array[ComponentView] = initViews

  /** Is the check complete? */
  private var done = new AtomicBoolean(false)

  /** Print information, and update variables for the start of the next ply.  In
    * particular, set done if all threads should terminate. */
  private def startOfPly(bound: Int) = {
    ply += 1
    if(newViews.isEmpty || ply > bound) done.set(true)
    else{
      println("\nSTEP "+ply)
      println("#abstractions = "+printLong(sysAbsViews.size))
      println(s"#transitions = ${printLong(transitions.size)}")
      println(s"#transition templates = ${printLong(transitionTemplates.size)}")
      println("#new active abstract views = "+printInt(newViews.size))
      nextNewViews = new BasicHashSet[ComponentView]
      newTransitions = new BasicHashSet[Transition]
      newTransitionTemplates = new BasicHashSet[TransitionTemplate]
    }
  }

  private def endOfPly() = {
    // Add views and transitions found on this ply into the main set.
    val newViewsAB = new ArrayBuffer[ComponentView]

    /* Add v to sysAbsViews and newViewsAB if new.  Return true if so. */
    def addView(v: ComponentView): Boolean = {
      if(sysAbsViews.add(v)){
        assert(v.representableInScript); newViewsAB += v; true
      }
      else false
    } // end of addView

    // Store transitions
    print(s"\nCopying: newTransitions, ${newTransitions.size}; ")
    for(t <- newTransitions.iterator){
      assert(transitions.add(t))
      for(v0 <- t.post.toComponentView){
        val v = Remapper.remapView(v0)
        if(addView(v)){
          v.setCreationInfo(t.pre, t.e, t.post)
          if(showTransitions) println(s"${t.toString}\ngives $v")
        }
      }
    }

    // Store transition templates
    print(s"newTransitionTemplates, ${newTransitionTemplates.size}; ")
    for(template <- newTransitionTemplates.iterator)
      transitionTemplates.add(template)

    // Store new views
    println(s"nextNewViews, ${nextNewViews.size}.")
    for(v <- nextNewViews.iterator) addView(v)

    // And update for next ply
    newViews = newViewsAB.toArray; nextIndex.set(0)
    if(showEachPly)
      println("newViews =\n"+newViews.map(_.toString).sorted.mkString("\n"))
  }

  @inline private def tryDebug(view: ComponentView) = {
    if(!done.getAndSet(true)){
      val debugger = new Debugger(system, sysAbsViews, initViews)
      debugger(view)
      // When the user is done, the debugger exits the whole system.
      sys.error("Unreachable") // This should be unreachable.
    }
    else{ } // Another thread found error
  }

  /** Output at end of check. */
  private def endOfCheck(bound: Int) = {
    // println("\nSTEP "+ply+"\n")
    // Following are expensive and verbose so normally disabled
    if(singleRef && doSanityCheck && bound == Int.MaxValue) EffectOn.sanityCheck
    if(singleRef && reportEffectOn) EffectOn.report
    if(showViews) println(sysAbsViews)
    // Summary 
    println("#abstractions = "+printLong(sysAbsViews.size))
    println(s"#transitions = ${printLong(transitions.size)}")
    println(s"#transition templates = ${printLong(transitionTemplates.size)}")
    println(s"#ServerStates = ${ServerStates.count}")
    println(s"#States = ${MyStateMap.stateCount}")
    // println(s"effectOnStore size = "+effectOnStore.size)
  }

  /** Index of next view in the current ply. */
  private val nextIndex = new AtomicInteger(0)

  /** Run the checker. 
    * @param bound the number of plys to explore (with negative values meaning 
    * effectively infinite).  */
  def apply(bound: Int = Int.MaxValue) = {
    ply = 0
    // Barrier for coordinating workers. 
    val barrier = new Barrier(numWorkers)
    val barrier1 = new WeakBarrier(numWorkers)

    /* A worker with identity me.  Worker 0 coordinates. */
    def worker(me: Int) = {
      var myDone = false
      while(!myDone){
        // Worker 0 resets for the next ply; the others wait.
        if(me == 0) startOfPly(bound)
        // barrier.sync(me) // 
        barrier1.sync//(me)
        if(!done.get){
          var donePly = done.get // if done, we exit loop
          // We need to perform four operations on each view in newViews.
          // Each operation will constitute a single task.  Each task
          // corresponds to a number i in [0..4*length), with i/length
          // indicating the operation, and i%length indicating the view.
// IMPROVE: if !singleRef, only need 3*length
          val length = newViews.length
          while(!donePly && !done.get){
            val i = nextIndex.getAndIncrement()
            if(i < 4*length){
              val opIx = i/length; 
              val viewIx = i%length; val view = newViews(viewIx)
              if(viewIx > 0 && viewIx%5000 == 0){ 
                print("."); if(viewIx%50000 == 0) print(s"${viewIx/1000}K") 
              }
              if(viewIx == 0) print(s"[$opIx]")
              opIx match{
                case 3 => // Process view transitions
                  if(processViewTransitions(view)) tryDebug(view)
                case 0 => // Effect of previous transitions on this view
                  effectOfPreviousTransitions(view)
                case 1 =>    // Effect of previous transition templates
                  instantiateTransitiontemplates(view)
                case 2 => 
                  if(singleRef) EffectOn.completeDelayed(view, nextNewViews)
              } // end of match
            }
            else donePly = true
          }
/*
          // Process all views from newViews.
          while(!donePly && !done.get){
            val i = nextIndex.getAndIncrement()
            if(i < newViews.length){
              if(process(newViews(i))){
                if(!done.getAndSet(true)){
                  val debugger = new Debugger(system, sysAbsViews, initViews)
                  debugger(newViews(i))
                  // When the user is done, the debugger exits the whole system.
                  sys.error("Unreachable") // This should be unreachable.
                }
                else{ } // Another thread found error
              }
              if(i > 0 && i%5000 == 0){ 
                print("."); if(i%50000 == 0) print(s"${i/1000}K") 
              }
            }
            else donePly = true
 */
 //         } // end of inner while

          // Wait for other workers to finish; then worker 0 resets for next ply.
          barrier.sync(me)
          // barrier1.sync
          if(me == 0) endOfPly()
        } // end of if(!done.get)
        else myDone = true
      } // end of main loop
    } // end of worker

    // Run numWorker workers
    Concurrency.runIndexedSystem(numWorkers, worker)

    endOfCheck(bound)
  } 


  /** Perform a memory profile of this. */
  def memoryProfile = {
    import ox.gavin.profiling.MemoryProfiler.traverse
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
    if(true){ traverse("system", system, maxPrint = 0); println() }
    else println("Omitting system\n") 
    EffectOn.memoryProfile; println()
    traverse("checker", this, maxPrint = 0); println()
  }
}






