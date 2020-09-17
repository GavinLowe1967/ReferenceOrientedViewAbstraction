package ViewAbstraction

import scala.collection.mutable.ArrayBuffer
import java.util.concurrent.atomic.{AtomicLong,AtomicInteger,AtomicBoolean}

import ox.gavin.profiling.Profiler

/** A checker for the view abstraction algorithm, applied to system.
  * @param aShapes the shapes of abstractions.
  * @param cShapes the shapes of concretizations. */
class Checker(system: System)
{
  // is there a three-way synchronisation between two components and a server?
  private val threeWaySync = system.threeWaySyncFound

  // val k = aShapes.head.sum; val l = cShapes.head.sum
  // println(s"k = $k; l = $l")

  /** The abstract views. */
  var sysAbsViews: ViewSet = null

  /** The concretizations. */
  var sysConcViews: ViewSet = null 

  /** The first view extender. */
  // var nve1: NewViewExtender = null

  // /** The second view extender. */
  // var nve2: NewViewExtender = null

  val Million = 1000000

  private var done = new AtomicBoolean(false); private var ply = 1

  /** Run the checker. 
    * @param bound the number of plys to explore (with negative values meaning 
    * effectively infinite).  */
  def apply(bound: Int = -1, verbose: Boolean = false)  = {

    // Get the initial views
    val (sav, initViews) = system.initViews; sysAbsViews = sav
    var newViews: Array[View] = initViews

    while(!done.get && ply != bound){
      println("\nSTEP "+ply) 
      println("#abstractions = "+printLong(sysAbsViews.size))
      println("#new active abstract views = "+printInt(newViews.size))
      val nextNewViews = new ArrayBuffer[View]
      for(v <- newViews) process(nextNewViews, v)
      ply += 1; newViews = nextNewViews.toArray; 
      if(newViews.isEmpty) done.set(true)
    }

  }

  /** Process v, calculating all the concrete transitions from v, adding the
    * post-states to sysAbsViews, and adding new ones to nextNewViews.
    */
  private def process(nextNewViews: ArrayBuffer[View], v: View) = { 
    println(s"\nProcessing $v")

    /* Add the principal component view of conc to sysAbsViews, and nextNewViews
     * if new. */
    def addView(conc: Concretization) = {
      val v1 = Remapper.remapComponentView(conc.toComponentView)
      print(v1)
      if(sysAbsViews.add(v1)){ println(".  Added."); nextNewViews += v1 }
      else println(".  Already present.")
    }

    v match{
      case cv: ComponentView =>
        val trans = system.transitions(cv)
        for((pre, e, post, outsidePids) <- trans){ // FIXME: not all transitions
          // Calculate all views corresponding to post.
          println(s"$pre -${system.showEvent(e)}-> $post ["+
            outsidePids.map(State.showProcessId)+"]")
          assert(pre.components(0) == cv.principal)
          val princ1 = post.components(0)

          // Case 1: component view for cv.principal
          val otherIds = post.components.tail.map(_.componentProcessIdentity)
          val newPids: Array[ComponentProcessIdentity] = 
            princ1.processIdentities.tail.filter(p => !otherIds.contains(p))
          if(newPids.nonEmpty) 
            println(s"newPids = "+newPids.map(State.showProcessId).mkString(","))
          if(newPids.forall{case (f,id) => isDistinguished(id)}){
            // Case 1(a): no new nondistinguished parameter
            assert(outsidePids.isEmpty) // FIXME
            addView(post)
            // Effect on other views of this transition.
            effectOnOthers(cv, post, nextNewViews)
          }
          else{ // Case 1(b): one new parameter from outside the view
            assert(newPids.length == 1) // FIXME
            assert(outsidePids.sameElements(newPids), 
              s"newPids = ${newPids.map(State.showProcessId).mkString(",")}; "+
                s"outsidePids = ${outsidePids.map(State.showProcessId)}")
            val outsidePid = outsidePids.head
            // Find all states for outsidePid, consistent with cv, that can
            // perform e, and their states after e.

            for((outsideSt, outsidePosts) <- consistentStates(outsidePid, cv, e);
              postSt <- outsidePosts){
              println(s"Outside transition $outsideSt "+
                s"-${system.showEvent(e)}-> $postSt")
              val extendedConc = post.extend(postSt)
              println(s"extendedConc = $extendedConc") 
              addView(extendedConc)
              // Effect on other views of this transition.
              effectOnOthers(cv, extendedConc, nextNewViews)
// ???
            }
          } // end of else


        } // end of for((pre, e, post, outsidePids) <- trans)
    }
  } // FIXME

  /** Effect on other views of a transition from cv that produces post.  For
    * every view v1 in sysAbsViews, if it is consistent with cv
    * (i.e. unifiable), and contains at least one process that changes state,
    * then update as per this transition. */
  private def effectOnOthers(
    cv: ComponentView, post: Concretization, nextNewViews: ArrayBuffer[View]) 
      = {
    for(v1 <- sysAbsViews.toArray) v1 match{ // IMPROVE iteration
      case cv1: ComponentView  =>
// FIXME: should be dealing with the concretizations here? 
        if(cv1.servers == cv.servers){
          println(s"Effect on $cv1");
          // IMPROVE if nothing changed state.
          val newCpts = Remapper.combine(cv, cv1)
          for((cpts, unifs) <- newCpts){
            println((cpts.mkString("[",",","]"), unifs))
            // For each (i1,i2) in unifs, replace cpts(i2) with
            // post.components(i1).  IMPROVE if component didn't change state.
            val cpts1 =
              if(unifs.isEmpty) cpts
              else Array.tabulate(cpts.length){ i =>
                val matches = unifs.filter(_._2 == i)
                if(matches.nonEmpty){
                  assert(matches.length == 1); val i1 = matches.head._1
                  val c1 = post.components(i1)
                  println(s"  Replaced ${cpts(i)} with ${c1}")
                  c1
                }
                else cpts(i)
              }
            val nv = Remapper.remapComponentView(
              new ComponentView(post.servers, cpts1(0), cpts1.tail) )
            print(s"  -> $nv.  ")
            if(sysAbsViews.add(nv)){
              println("Added.")
              if(system.isActive(nv)) nextNewViews += nv
            }
            else println("Already present.")
          }
        }
    } // end of match
  }
          // IMPROVE: need better way of iterating over ViewSet

  /** Find all states of component pid consistent with cv that can perform event
    * e, and the states those reach after e.  Consistent here means that there
    * is a view v1 in sysAbsViews and a renaming pi such that pi(v1) contains
    * the state of pid, agrees with v on common components, and every view of
    * pi(v1) U v is in sysAbsViews.  Pre: pid is not in cv. */
  private def consistentStates(
    pid: ComponentProcessIdentity, cv: ComponentView, e: EventInt)
      : ArrayBuffer[(State, List[State])] = {
    val result = new ArrayBuffer[(State, List[State])]()
    val (f,id) = pid; val servers = cv.servers; val components = cv.components
    for(v1 <- sysAbsViews.toArray) v1 match{ // IMPROVE iteration
      case cv1: ComponentView =>
        if(cv1.servers == servers) 
          system.consistentStates(pid, cv, e, cv1, result)
    } // end of match/for(v1 <- ...)
    // println(s"conistentStates result: "+result.mkString("; "))
    result
  }




    // sysConcViews = 
    //   if(memoryless) new ImplicitSystemViewSet(sysAbsViews, aShapes)
    //   else SystemViewSet()

    // val initViews = sysAbsViews.toArray 
    // println("init:\n" + sysAbsViews.mkString("\n"))
    // All shapes formed by adding one component to a shape from aShapes
    // var midShapes = List[Array[Int]]()
    // if(threeWaySync){
    //   for(sh <- aShapes; i <- 0 until numTypes){
    //     val newShape = sh.clone; newShape(i) += 1
    //     if(midShapes.forall(sh1 => !sh1.sameElements(newShape)))
    //       midShapes ::= newShape
    //   }
    //   println("midShapes = "+midShapes.map(_.mkString("<", ",", ">")))
    // }
    // // View extender to extend from aShapes to midShapes
    // val midViews = 
    //   if(threeWaySync){ 
    //     if(memoryless) new ImplicitSystemViewSet(sysAbsViews, aShapes)
    //     else SystemViewSet() 
    //   } 
    //   else null
    // nve1 =
    //   if(!threeWaySync)
    //     new NewViewExtender(sysConcViews, aShapes, cShapes)
    //   else{
    //     assert(numTypes <= 2)
    //     new NewViewExtender(midViews, aShapes, midShapes, firstStep = true)
    //   }
    // // View extender to extend from midShapes to cShapes
    // nve2 = 
    //   if(!threeWaySync) null
    //   else new NewViewExtender(sysConcViews, midShapes, cShapes)

    // // The gamma function applied to sv
    // @inline def gamma(sv: SystemView, prevPosts: SystemViewSet)
    //     : ArrayBuffer[SystemView] = {
    //   assert(memoryless == (prevPosts == null))
    //   if(!threeWaySync) nve1.gamma(sv, prevPosts)
    //   else{
    //     val newMidViews = nve1.gamma(sv, null)
    //     nve2.gammaAll(newMidViews, prevPosts)
    //   }
    // }


    // // New abstract views seen for the first time on the last iteration
    // var newViews: Array[SystemView] = initViews

    // // Code common to both new and old styles. 
    // /* Start of each ply. */
    // @inline def preamble() = {
    //   println("\nSTEP "+ply)
    //   println("#concretizations = "+printLong(sysConcViews.size))      
    //   println("#abstractions = "+printLong(sysAbsViews.size))
    //   println("#new abstract views = "+printInt(newViews.size))
    //   print("Checking: ")
    // }

    // /* Reporting at end of each ply. */
    // @inline def report() = {
    //   println
    //   if(threeWaySync) println("mid states = "+printLong(midViews.size))
    //   if(true){
    //     val ReportSlots = false // for profiling of memory usage
    //     println("state count = "+printInt(State.stateCount))
    //     println("server state count = "+ServerStates.count)
    //     println("server transStoreSize = "+system.servers.transStoreSize)
    //     print("nve1.size = "+printInt(nve1.size)+
    //             "; stateCount = "+printLong(nve1.stateCount))
    //     if(ReportSlots) println("; slots = "+printLong(nve1.slotCount)) 
    //     else println
    //     if(nve2 != null){
    //       print("nve2.size = "+printInt(nve2.size)+
    //                 "; stateCount = "+printLong(nve2.stateCount))
    //       if(ReportSlots) println("; slots = "+printLong(nve2.slotCount)) 
    //       else println
    //     }
    //   }
    // } // end of report

    // Main code

    // If memoryless, number of posts found on most recent ply.  Note: if a
    // concretization c is found by post, and c has an abstraction that was
    // previously newly found on this ply, then c will not be counted in
    // thisPostCount, but will be counted under gamma in the next ply.
  //   val thisPostCount = if(memoryless) new AtomicInteger(0) else null
  //   // Abstract views to expand on the next ply.
  //   var nextNewViews = new ShardedConcBuffer[SystemView]
  //   // If !memoryless, concretizations found by gamma on this ply (including
  //   // those found by post on previous ply).  This avoids repetitions.
  //   var theseConcs = if(memoryless) null else SystemViewSet()
  //   // Counts of abstractions processed, and concretizations produced by gamma.
  //   val thisIterCount = new AtomicInteger(0)
  //   val thisGammaCount = new AtomicLong(0)
  //   // Barrier for synchronising in each round.
  //   val barrier = new Concurrency.Barrier(numThreads)
  //   // Index of start of next task; size of each task
  //   val taskCount = new AtomicInteger(0); val TaskSize = 5
  //   var len = newViews.length
  //   preamble()

  //   /* Process a single SystemView. */
  //   @inline def process(sv: SystemView) = if(!done.get){
  //     val iter = thisIterCount.incrementAndGet
  //     if(iter%1000 == 0){
  //       if(iter%10000 == 0) print(s"${iter/1000}K") else print(".")
  //     }
  //     // -------------- Gamma
  //     val newConcs: ArrayBuffer[SystemView] = gamma(sv, theseConcs)
  //     // for(sv1 <- newConcs){
  //     //   assert(sv1.componentView.length == l)
  //     //   val shape = Views.shape(sv1.componentView)
  //     //   assert(cShapes.exists(_.sameElements(shape)))
  //     // }
  //     // As each ply progresses, the rate of progress over newConcViews
  //     // slows, but the rate of production stays fairly constant.
  //     val oldGammaCount = thisGammaCount.getAndAdd(newConcs.length)
  //     val newGammaCount = oldGammaCount+newConcs.length
  //     if(if(oldGammaCount < 100*Million)
  //          oldGammaCount/Million != newGammaCount/Million
  //        else oldGammaCount/(10*Million) != newGammaCount/(10*Million))
  //       print(Console.BLUE+"<"+newGammaCount/Million+"M>"+Console.BLACK)
  //     // Note: each concretization produced by post on the previous ply
  //     // will be recreated by a call to gamma1 on this ply.
  //     // ---------- Post
  //     val (posts, errors, deadlocks) = system.post(newConcs, sysConcViews)
  //     // for(sv1 <- postsA){
  //     //   assert(sv1.componentView.length == l)
  //     //   val shape = Views.shape(sv1.componentView)
  //     //   assert(cShapes.exists(_.sameElements(shape)))
  //     // }
  //     if(memoryless) thisPostCount.getAndAdd(posts.length)
  //     // Handling errors
  //     if(errors.nonEmpty){
  //       if(!done.getAndSet(true)){ // we're the first to find an error
  //         println("error event possible from:\n"+errors.head)
  //         println(s"${errors.length} error states")
  //         val debugger = new Debugger(system, threeWaySync, aShapes,
  //                                     sysAbsViews, initViews.toList, false)
  //         debugger(errors.head)
  //       }
  //     }
  //     else if(deadlocks.nonEmpty){
  //       if(!done.getAndSet(true)){ // we're the first to find an error
  //         println("deadlock in:\n" + deadlocks.head)
  //         println(s"${deadlocks.length} deadlocked states")
  //         val debugger = new Debugger(system, threeWaySync, aShapes,
  //                                     sysAbsViews, initViews.toList, true)
  //         debugger(deadlocks.head)
  //       }
  //     }
  //     else{
  //       // -------- Alpha
  //       val myNewViews = system.alpha(aShapes, posts, sysAbsViews, ply)
  //       for(sv1 <- myNewViews) nextNewViews.put(sv1)
  //     }
  //   } // end of process

  //   /* A single worker. */
  //   def worker(me: Int) = {
  //     while(!done.get && ply != bound){
  //       // Process tasks until all complete
  //       var taskStart = taskCount.getAndAdd(TaskSize)
  //       while(taskStart < len){
  //         for(i <- taskStart until (taskStart+TaskSize min len))
  //           process(newViews(i))
  //         taskStart = taskCount.getAndAdd(TaskSize)
  //       }

  //       barrier.sync() // wait for other workers to finish
  //       if(me == 0){ // reset for next round IMPROVE: split between workers
  //         ply += 1; newViews = nextNewViews.get; len = newViews.length
  //         taskCount.set(0)
  //         if(newViews.isEmpty) done.set(true)
  //         report()
  //         if(!done.get){
  //           preamble()
  //           nextNewViews = new ShardedConcBuffer[SystemView]
  //           // We're about to double-count the post states from the previous
  //           // round.
  //           if(memoryless){
  //             sysConcViews.addCount(-thisPostCount.get); thisPostCount.set(0)
  //           }
  //           else theseConcs = SystemViewSet()
  //           thisIterCount.set(0); thisGammaCount.set(0)
  //         }
  //       }
  //       // mustn't allow workers to read ply or done before above completed
  //       barrier.sync()
  //     }
  //   }

  //   // Release the workers!
  //   Concurrency.runIndexedSystem(numThreads, worker)

  //   // println(sysConcViews.reportSizes.mkString(", "))
  //   println("Explored "+printLong(sysConcViews.size)+" concretizations and "+
  //             printLong(sysAbsViews.size)+" abstractions.")
  //   // if(nve2 != null) nve2.profile else nve1.profile
  // }



}

