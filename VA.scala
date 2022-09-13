package ViewAbstraction

// import ox.cads.util.{SamplingProfiler,ProfilerSummaryTree}
import ox.gavin.profiling.{SamplingProfiler,ProfilerSummaryTree}
import scala.collection.mutable.ArrayBuffer

object VA{ 
  /** Model of the system. */
  var system: SystemP.System = null // public for profiling

  /** The checker. */
  var checker: Checker = null

  /** Run a check.  Called by ScalaInstrumentation. */
  def check(fname: String, bound: Int, singleRefX: Boolean, numWorkersX: Int)
      : Unit = {
    singleRef = singleRefX; numWorkers = numWorkersX
    system = new SystemP.System(fname); println("Created system")
    // Create and run the checker
    checker = new Checker(system, numWorkers); checker(bound = bound)
    doMemoryProfile
  }

  /** Print a time given in nanoseconds. */
  private def printTime(time: Long) = {
    val millis = time/1_000_000 // in ms
    if(millis >= 100_000){
      println(s"${millis/1000}s")
      if(millis >= 1_000_000) println(s"${millis/60_000}min")
    }
    else println(s"${millis}ms")
  }

  // Parameters of profiling.
  var profiling = false; var profilingFlat = false; var interval = 20
  var profilingBoth = false;

  /** Get the profiler. */
  def getProfiler: SamplingProfiler = {
    def filter(frame: StackTraceElement) : Boolean =
      SamplingProfiler.defaultFilter(frame) && 
        !frame.getClassName.contains("jdk.internal") ||
        frame.getClassName.contains("Profiler") && frame.getMethodName == "count"
    val printer =
      if(profilingBoth){
        data: ArrayBuffer[SamplingProfiler.StackTrace] => {
          SamplingProfiler.printTree(
            filter = filter,
            expand = ProfilerSummaryTree.expandToThreshold(0.05))(data) +
          SamplingProfiler.print(filter = filter, length = 60)(data)
        }
      }
      else if(!profilingFlat)
        SamplingProfiler.printTree(
          filter = filter,
          expand = ProfilerSummaryTree.expandToThreshold(0.05)) _
      else SamplingProfiler.print(filter = filter, length = 60) _
    new SamplingProfiler(interval = interval, print = printer)
  }

  var bound = Int.MaxValue // bound on check
  // var numWorkers = 1
  var testing = false // Are we running the unit tests?
  var memoryProfile = false // Are we doing memory profiling?

  /** Run a test on fname. */
  def run(fname: String): Long = {
    val start = java.lang.System.nanoTime
    system = new SystemP.System(fname)
    // Create and run the checker
    checker = new Checker(system, numWorkers)
    print("Compiled for "); printTime(java.lang.System.nanoTime-start)
    checker(bound = bound)
    checker.numViews
  }

  import ox.gavin.profiling.MemoryProfiler.traverse

  /** Run the memory profiler. */
  private def doMemoryProfile = {
    checker.memoryProfile
    // traverse("Combiner", CombinerP.Combiner, maxPrint = 0); println
    traverse("VA", this, maxPrint = 0, ignore = List("System"))
  }

  /** The output of profiling. */
  private def profileReport = {
    ox.gavin.profiling.Profiler.report 
    if(memoryProfile) checker.memoryProfile
    if(!testing){ // checker is null when testing
      // println(s"checker.effectOnOthersCount = "+
      //   printLong(checker.effectOnOthersCount))
      // println(s"checker.effectOfPreviousTransitionsCount = "+
      //   checker.effectOfPreviousTransitionsCount)
      // println(s"checker.newViewCount = "+printLong(checker.newViewCount))
      // println("checker.addedViewCount = "+printLong(checker.addedViewCount))
      println("checker.addTransitionCount = "+
        printLong(checker.addTransitionCount))
      // println("checker.instantiateTransitionTemplateCount = "+
      //   printLong(checker.instantiateTransitionTemplateCount))
    }
  }

  // Test suite: list of filenames and expected number of states; first for
  // full views then for singleRef.
  val testSuite =  List(
    ("CSP/lockBasedStack.csp", 302), ("CSP/lockBasedQueue.csp", 556),
    ("CSP/TreiberStack.csp", 1653), ("CSP/lockFreeQueue.csp", 2272),
    ("CSP/TreiberStackOmitCreator.csp", 1125)
  )
  val srTestSuite = 
    // The switch below corresponds to the switch in StateArray.crossRefs
    if(StateArray.CrossRefFlag) List(
      ("CSP/lockBasedStack.csp", 294), ("CSP/lockBasedQueue.csp", 553),
      ("CSP/TreiberStack.csp", 1072), // 1075 if clause (3) in MissingCommon omitted
      ("CSP/lockFreeQueue.csp", 2210)// , ("CSP/TreiberStackOmitCreator.csp", 889)
    )
  else List(
    ("CSP/lockBasedStack.csp", 306), ("CSP/lockBasedQueue.csp", 570),
    ("CSP/TreiberStack.csp", 1072), // 1075 if clause (3) in MissingCommon omitted
    ("CSP/lockFreeQueue.csp", 2210) //, ("CSP/TreiberStackOmitCreator.csp", 889)
  )


  /** Run a test suite. */
  def runTestSuite() = {
    val theTestSuite = if(singleRef) srTestSuite else testSuite
    for((fname, states) <- theTestSuite){
      State.reset; MyStateMap.reset; MissingCommon.reset; 
      MissingInfoStore.reset; EffectOn.reset; ThreadID.reset
      println("********* "+fname)
      val states1 = run(fname)
      assert(states == states1,
        s"$fname: expected $states states but found $states1.")
    }
  }

  /** Main function. */
  def main(args: Array[String]) = {
    // Parse arguments
    var i = 0; var fname = ""; var timing = false; var testSuite = false
    var reps = 1

    while(i < args.length) args(i) match{
      case "--profile" => profiling = true; interval = args(i+1).toInt; i += 2
      case "--profileFlat" =>
        profilingFlat = true; interval = args(i+1).toInt; i += 2
      case "--profileBoth" =>
        profilingBoth = true; interval = args(i+1).toInt; i += 2
      case "--verbose" => verbose = true; i += 1
      case "--bound" => bound = args(i+1).toInt; i += 2
      case "--timing" => timing = true; i += 1
      case "--noDebug" => debuggable = false; i += 1
      case "--test" => testing = true; i += 1
      case "--testSuite" => testSuite = true; i += 1
      case "--singleRef" => singleRef = true; i += 1
      case "--showViews" => showViews = true; i += 1
      case "--showEachPly" => showEachPly = true; i += 1
      case "--showTransitions" => showTransitions = true; i += 1
      case "--showRedundancies" => showRedundancies = true; i += 1
      // case "--reverseTransitionIter" => TransitionSet.reversed = true; i += 1
      case "--useOldViewSet" => UseNewViewSet = false; i += 1
      case "--doSanityCheck" => doSanityCheck = true; i += 1
      case "--reportEffectOn" => reportEffectOn = true; i += 1
      // case "--swapEndOfPly" => swappedEndOfPly = true; i += 1
      // case "--newEffectOn" => newEffectOn = true; i += 1
      case "--memoryProfile" => memoryProfile = true; i += 1
      case "--numWorkers" => numWorkers = args(i+1).toInt; i += 2
      case "--reps" => reps = args(i+1).toInt; i += 2
      case fn => 
        if(fn(0) == '-'){ println(s"Command not recognised: $fn"); sys.exit() }
        else{ fname = fn; i += 1 }
    }
    assert(fname.nonEmpty || testing || testSuite, "no filename specified")
    // println("numThreads = "+numThreads)
    println("numWorkers = "+numWorkers)
    // IMPROVE: we don't want both numWorkers and numThreads

    // Initialise Profiler. 
    ox.gavin.profiling.Profiler.setWorkers(numWorkers)
    val profiler = getProfiler
    // Run the check
    val start = java.lang.System.nanoTime
    try{
      if(testing){ 
        assert(fname.isEmpty)
        singleRef = false // tests assume this
        system = new SystemP.System("CSP/test-file.csp")
        // TestStates.report
        new CompileTest(system.fdrEvents).test
        UnificationTest.test
        RemapperP.RemapperTest.test; CombinerP.CombinerTest.test
        SystemP.SystemTest.test(system); 
        new ExtendabilityP.ExtendabilityTest(system).test
        new CheckerTest(system, numWorkers).test
        RemappingExtenderTest()
        SingleRefEffectOnUnificationTest()
      }
      else if(testSuite){ 
        assert(fname.isEmpty)
        println(s"reps = $reps")
        for(_ <- 0 until reps) runTestSuite()
      }
      else if(profiling || profilingFlat || profilingBoth) profiler(run(fname)) 
      else run(fname)
      val elapsed0 = (java.lang.System.nanoTime - start) // in ns
      if(timing) println(elapsed0) else printTime(elapsed0)
    }
    finally{ if(system != null) system.finalise }
 
    profileReport
    if(!timing) println("goodbye")
  }


}
 
 
