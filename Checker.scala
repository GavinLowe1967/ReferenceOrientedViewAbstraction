package ViewAbstraction

import collection.{MyHashSet,BasicHashSet,ShardedHashSet}
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

  /** The state of the checker. */
  protected var checkerState = new CheckerState(system, sav)

  def numViews = checkerState.numViews

  // def addTransitionCount = checkerState.addTransitionCount

  // ========= Main function

  /** The views to be expanded on the current ply. */
  private var newViews: Array[ComponentView] = initViews

  /** Is the check complete? */
  private var done = new AtomicBoolean(false)

  /** Print information, and update variables for the start of the next ply.  In
    * particular, set done if all threads should terminate.  Performed by
    * worker 0.  */
  private def startOfPly(bound: Int) = {
    if(ply != 0){ 
      // Views for workers to work on in this ply. 
      newViews = checkerState.getNewViews; nextIndex.set(0)
      if(showEachPly)
        println("newViews =\n"+newViews.map(_.toString).sorted.mkString("\n"))
      // if(singleRef && doSanityCheck && useNewEffectOnStore)
      //   NewEffectOn.sanityCheck(checkerState.sysAbsViews)
    }
    ply += 1
    if(newViews.isEmpty || ply > bound) done.set(true)
    else{
      println("\nSTEP "+ply)
      checkerState.startOfPly
      println("#new active abstract views = "+printInt(newViews.size))
    }
  }

  /** Produce debugger, based on view,unless another thread has got here
    * first. */
  @inline private def tryDebug(view: ComponentView) = {
    if(!done.getAndSet(true)){
      val debugger = new Debugger(system, checkerState.sysAbsViews, initViews)
      debugger(view)
      // When the user is done, the debugger exits the whole system.
      sys.error("Unreachable") // This should be unreachable.
    }
    else{ } // Another thread found error
  }

  /** Output at end of check. */
  private def endOfCheck(bound: Int) = {
    println()
    // Following are expensive and verbose so normally disabled
    if(singleRef && doSanityCheck && bound == Int.MaxValue){
      if(useNewEffectOnStore) NewEffectOn.sanityCheck(checkerState.sysAbsViews)
      else SingleRefEffectOn.sanityCheck
    }
    if(singleRef && reportEffectOn){
      if(useNewEffectOnStore) NewEffectOn.report else SingleRefEffectOn.report
    }
    checkerState.endOfCheck
    println(s"#ServerStates = ${ServerStates.count}")
    println(s"#States = ${MyStateMap.stateCount}")
  }

  /** Index of next view in the current ply. */
  private val nextIndex = new AtomicInteger(0)

  /** Barrier for coordinating workers. */
  private val barrier = new Barrier(numWorkers)
    //val barrier1,barrier2 = new WeakBarrier(numWorkers)

  /** Bound on the number of plies. */
  private var bound = Int.MaxValue

  /* A worker with identity me.  Worker 0 coordinates. */
  def worker(me: Int) = {
    var myDone = false
    while(!myDone){
      // Worker 0 resets for the next ply; the others wait.
      if(me == 0) startOfPly(bound)
      barrier.sync(me) 
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
                if(checkerState.processViewTransitions(view)) tryDebug(view)
              case 3 => // Effect of previous transitions on this view
                checkerState.effectOfPreviousTransitions(view)
              case 2 =>    // Effect of previous transition templates
                checkerState.instantiateTransitiontemplates(view)
              case 0 =>
                if(singleRef){
                  if(useNewEffectOnStore)
                    NewEffectOn.completeDelayed(view, checkerState.nextNewViews)
                  else SingleRefEffectOn.completeDelayed(
                    view, checkerState.nextNewViews)
                }
            } // end of match
          }
          else donePly = true
        }
// IMPROVE: if done here because another thread has found an error, then exit
        // Wait for other workers to finish; then worker 0 resets for next ply.
        barrier.sync(me)
        checkerState.endOfPly(me)
        // Sync before next round
        barrier.sync(me)
      } // end of if(!done.get)
      else myDone = true
    } // end of main loop
  } // end of worker

  /** Run the checker. 
    * @param bound the number of plys to explore (with negative values meaning 
    * effectively infinite).  */
  def apply(bound: Int = Int.MaxValue) = {
    this.bound = bound; ply = 0
    ThreadID.reset

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
    traverse("StateArray", StateArray, maxPrint = 1)
    if(false){ traverse("system", system, maxPrint = 0); println() }
    else println("Omitting system\n") 
    traverse("ServerStates", ServerStates, maxPrint = 0); println()
    //traverse("first view", sysAbsViews.iterator.next(), maxPrint = 0); println()
    println("ReducedComponentView size = "+ReducedComponentView.size)
    traverse("ReducedComponentView", ReducedComponentView, maxPrint = 0)
    println()
    checkerState.memoryProfile
    // // Traverse 3 views.  Not very useful as mostly in creationIngredients.
    // val viewsIter = sysAbsViews.iterator
    // for(_ <- 0 until 3; if viewsIter.hasNext){
    //   traverse("ComponentView", viewsIter.next(), maxPrint = 1); println()
    // }
    // traverse("sysAbsViews", sysAbsViews, maxPrint = 1); println()
    // traverse("transitions", transitions, maxPrint = 0); println()
    // traverse("transitionTemplates", transitionTemplates, maxPrint = 0); println()
    // // traverse("extendability", extendability, maxPrint = 0); println()
    // traverse("transitionTemplateExtender", transitionTemplateExtender, 
    //   maxPrint = 1, ignore = List("System"))
    // println()
    if(singleRef){
      if(useNewEffectOnStore) NewEffectOn.memoryProfile
      else SingleRefEffectOn.memoryProfile
      println()
    }
    traverse("checker", this, maxPrint = 1, ignore = List("System")); println()
    // Below here should be trivial
    traverse("CompatibleWithCache", CompatibleWithCache, maxPrint = 0)
    traverse("Combiner", CombinerP.Combiner, maxPrint = 0)
    traverse("ComponentView0", ComponentView0, maxPrint = 0)
    traverse("ComponentView", ComponentView, maxPrint = 0)
    traverse("Concretization", Concretization, maxPrint = 0)
    traverse("Concurrency", Concurrency, maxPrint = 0)
    traverse("EffectOn", EffectOn, maxPrint = 0, ignore = List("System"))
    traverse("EffectOnStore", EffectOnStore, maxPrint = 0)
    traverse("EffectOnUnification", EffectOnUnification, maxPrint = 0)
    traverse("FDRTransitionMap", FDRTransitionMap, maxPrint = 0)
    traverse("MissingInfo", MissingInfo, maxPrint = 0)
    traverse("Pools", Pools, maxPrint = 0)
    traverse("Remapper", Remapper, maxPrint = 0)
    traverse("ServerBasedViewSet", ServerBasedViewSet, maxPrint = 0)
    traverse("ServersReducedMap", ServersReducedMap, maxPrint = 0)
    traverse("SingleRefEffectOnUnification", SingleRefEffectOnUnification, maxPrint = 0)
    traverse("State", State, maxPrint = 0)
    traverse("Transition", Transition, maxPrint = 0)
    traverse("TransitionSet", TransitionSet, maxPrint = 0)
    traverse("TransitionTemplateSet", TransitionTemplateSet, maxPrint = 0)
    traverse("Unification", Unification, maxPrint = 0)
    traverse("View", View, maxPrint = 0)
    traverse("ViewSet", ViewSet, maxPrint = 0)
    val others = List(
      Profiler, Concretization, Debugger, FDRTransitionMap,
      MissingCommon, MissingInfoStore, ServerBasedViewSet, ThreadID,
      collection.IntSet, collection.LockFreeReadHashSet, 
      collection.ShardedHashMap, collection.ShardedHashSet)
    for(obj <- others)  traverse(obj.toString, obj, maxPrint = 0)
  }
}






