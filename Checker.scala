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

  protected type NextNewViewSet = MyShardedHashSet[ComponentView]

  /** The new views to be considered on the next ply. */
  protected var nextNewViews: NextNewViewSet = null

  /* The transitions found so far. */
  private val transitions = new NewTransitionSet

  private type NextTransitionSet = MyShardedHashSet[Transition]

  /** Transitions found on this ply.  Transitions are initially added to
    * newTransitions, but transferred to transitions at the end of the ply. */
  private var newTransitions: NextTransitionSet = null

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

  // /** Does the pre-state of a transition match cv, so the induced transition
  //   * will just reproduce the earlier transition? */
  // private def matches(pre: Concretization, cv: ComponentView) = {
  //   require(pre.servers == cv.servers)
  //   if(singleRef){
  //     val preCpts = pre.components; val cpts = cv.components
  //     false && preCpts.sameElements(cpts)
  //     // preCpts(0) == cpts(0) && preCpts.sameElements(cpts)
  //     // preCpts.length == cpts.length &&
  //       // (cpts.length == 1 || cpts(1) == preCpts(1))
  //   }
  //   else false
  // }

  /** Effect on other views of a transition t.  For every view v1 in
    * sysAbsViews, if it is consistent with t.pre (i.e. unifiable), and
    * contains at least one process that changes state, then update as per
    * this transition. */
  private def effectOnOthers(t: Transition) = if(t.pre != t.post){
    val highlight = false && Transition.highlight(t)
    if(highlight) println(s"effectOnOthers($t)")
    val iter = 
      if(UseNewViewSet) sysAbsViews.iterator(t)
      else sysAbsViews.iterator(t.preServers)
    while(iter.hasNext){ 
      val cv = iter.next()
      new EffectOn(t, cv, nextNewViews)()
      // if(highlight) println(cv)
    }
  }

  /** The effect of previously found extended transitions on the view cv. */
  private def effectOfPreviousTransitions(cv: ComponentView) = {
    val iter = transitions.iterator(cv)
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

  /** Producer for iterators for copying views found on one ply, ready for the
    * next ply.  Set by worker 0 on each ply. */
  private var viewShardIteratorProducer: 
      ShardedHashSet.ShardIteratorProducerT[ComponentView] = null

  private var transitionShardIteratorProducer: 
      ShardedHashSet.ShardIteratorProducerT[Transition] = null

  /** Buffer that accumulated views found on one ply for the next ply.
    * Protected by synchronized block IMPROVE*/
  // private var newViewsAB = new ArrayBuffer[ComponentView]
  private var viewsBuff: ConcurrentBuffer[ComponentView] = null

  /** Print information, and update variables for the start of the next ply.  In
    * particular, set done if all threads should terminate.  Performed by
    * worker 0.  */
  private def startOfPly(bound: Int) = {
    if(ply != 0){ 
      // Views for workers to work on in this ply. 
      newViews = viewsBuff.get; nextIndex.set(0)
      if(showEachPly)
        println("newViews =\n"+newViews.map(_.toString).sorted.mkString("\n"))
    }

    ply += 1
    if(newViews.isEmpty || ply > bound) done.set(true)
    else{
      println("\nSTEP "+ply)
      println("#abstractions = "+printLong(sysAbsViews.size))
      println(s"#transitions = ${printLong(transitions.size)}")
      println(s"#transition templates = ${printLong(transitionTemplates.size)}")
      println("#new active abstract views = "+printInt(newViews.size))
      nextNewViews = new NextNewViewSet
      newTransitions = new NextTransitionSet 
      newTransitionTemplates = new BasicHashSet[TransitionTemplate]

      // Initialise objects ready for end of ply
      viewsBuff = new ConcurrentBuffer[ComponentView](numWorkers)
      // newViewsAB = new ArrayBuffer[ComponentView]
      viewShardIteratorProducer = nextNewViews.shardIteratorProducer
      transitionShardIteratorProducer = newTransitions.shardIteratorProducer
      if(singleRef) EffectOn.prepareForPurge
    }
  }

  /** Add v to sysAbsViews and viewsBuff if new.  Return true if so. */
  private def addView(me: Int, v: ComponentView): Boolean = /*synchronized*/{
    if(ComponentView0.highlight(v)) println(s"adding $v")
    if(sysAbsViews.add(v)){
      // if(ComponentView0.highlight(v)) println(s"Added $v")
      assert(v.representableInScript); viewsBuff.add(me, v); true
    }
    else false
  } // end of addView


  /** Collectively, workers copy new views and transitions, at the end of a
    * ply. */
  private def endOfPly(me: Int) = {
    // Worker 0 copies transition templates.
    if(me == 0){
      print(s"\nCopying: nextNewViews, ${nextNewViews.size}; ")
      print(s"newTransitionTemplates, ${newTransitionTemplates.size}; ")
      println(s"newTransitions, ${newTransitions.size}. ")
      for(template <- newTransitionTemplates.iterator)
        transitionTemplates.add(template)
    }

    // Purges from the effectOnStore
// IMPROVE: only if enough views have been added since the last purge.
    if(singleRef) EffectOn.purge

    // Collectively copy views
    var iter = viewShardIteratorProducer.get
    while(iter != null){
      for(v <- iter) addView(me, v)
      iter = viewShardIteratorProducer.get
    }

    // Collectively copy transitions
    var transIter = transitionShardIteratorProducer.get
    while(transIter != null){
      for(t <- transIter){
        transitions.add(t)
        var vs = t.post.toComponentView
        while(vs.nonEmpty){
          val v0 = vs.head; vs = vs.tail; val v = Remapper.remapView(v0)
          if(addView(me, v)){
            v.setCreationInfo(t.pre, t.e, t.post)
            if(showTransitions) println(s"${t.toString}\ngives $v")
          }
        }
      } // end of iteration over transIter
      transIter = transitionShardIteratorProducer.get
    }
  }

  /** Produce debugger, based on view,unless another thread has got here
    * first. */
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
    println()
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
    //val barrier1,barrier2 = new WeakBarrier(numWorkers)

    /* A worker with identity me.  Worker 0 coordinates. */
    def worker(me: Int) = {
      var myDone = false
      while(!myDone){
        // Worker 0 resets for the next ply; the others wait.
        if(me == 0) startOfPly(bound)
        barrier.sync(me) // 
        // barrier2.sync//(me)
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
              if(viewIx > 0 && viewIx%10000 == 0){ 
                print("."); if(viewIx%100000 == 0) print(s"${viewIx/1000}K") 
              }
              if(viewIx == 0) print(s"[$opIx]")
              // Note: the order below doesn't matter for correctness, but
              // seems to make quite a big difference for performance.  Having
              // effectOfPreviousTransitions before processViewTransitions is
              // much slower.
              opIx match{
                case 1 => // Process view transitions
                  if(processViewTransitions(view)) tryDebug(view)
                case 3 => // Effect of previous transitions on this view
                  effectOfPreviousTransitions(view)
                case 2 =>    // Effect of previous transition templates
                  instantiateTransitiontemplates(view)
                case 0 => 
                  if(singleRef) EffectOn.completeDelayed(view, nextNewViews)
              } // end of match
            }
            else donePly = true
          } 
          // Wait for other workers to finish; then worker 0 resets for next ply.
          barrier.sync(me)
          // barrier1.sync
          endOfPly(me)
          // Sync before next round
          barrier.sync(me)
          // barrier1.sync // (me)
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
    if(true){ traverse("system", system, maxPrint = 0); println() }
    else println("Omitting system\n") 
    traverse("ServerStates", ServerStates, maxPrint = 0); println()
    //traverse("first view", sysAbsViews.iterator.next(), maxPrint = 0); println()
    traverse("sysAbsViews", sysAbsViews, maxPrint = 0); println()
    traverse("transitions", transitions, maxPrint = 0); println()
    traverse("transitionTemplates", transitionTemplates, maxPrint = 0); println()
    // traverse("extendability", extendability, maxPrint = 0); println()
    traverse("transitionTemplateExtender", transitionTemplateExtender, 
      maxPrint = 1, ignore = List("System"))
    println()
    EffectOn.memoryProfile; println()
    traverse("checker", this, maxPrint = 0); println()
    // Below here should be trivial
    traverse("CompatibleWithCache", CompatibleWithCache, maxPrint = 0)
    traverse("ComponentView0", ComponentView0, maxPrint = 0)
    traverse("ComponentView", ComponentView, maxPrint = 0)
    traverse("Concretization", Concretization, maxPrint = 0)
    traverse("Concurrency", Concurrency, maxPrint = 0)
    traverse("EffectOnUnification", EffectOnUnification, maxPrint = 0)
    traverse("FDRTransitionMap", FDRTransitionMap, maxPrint = 0)
    traverse("MissingInfo", MissingInfo, maxPrint = 0)
    traverse("ServersReducedMap", ServersReducedMap, maxPrint = 0)
    traverse("SingleRefEffectOnUnification", SingleRefEffectOnUnification, maxPrint = 0)
    traverse("State", State, maxPrint = 0)
    traverse("Transition", Transition, maxPrint = 0)
    traverse("TransitionSet", TransitionSet, maxPrint = 0)
    traverse("TransitionTemplateSet", TransitionTemplateSet, maxPrint = 0)
    traverse("Unification", Unification, maxPrint = 0)
    traverse("View", View, maxPrint = 0)
    traverse("ViewSet", ViewSet, maxPrint = 0)
  }
}






