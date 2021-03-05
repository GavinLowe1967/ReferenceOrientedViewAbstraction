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
  def check(fname: String, bound: Int,
            checkDeadlock: Boolean, significancePaths: List[SignificancePath]) 
      : Unit = {
    system = new SystemP.System(fname, checkDeadlock, significancePaths)

    // Create and run the checker
    println("Created system")
    checker = new Checker(system)
    checker(bound = bound)
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

  def main(args: Array[String]) = {
    // Parse arguments
    var i = 0
    var fname = ""; 
    var checkDeadlock = false
    var significancePaths: List[SignificancePath] = List()
    // var k = -1; var aShapes = List[Shape]()
    var profiling = false; var profilingFlat = false; var interval = 20
    var profilingBoth = false
    var verbose = false; var bound = Int.MaxValue; var timing = false
    var testing = false

    while(i < args.length) args(i) match{
      case "--significancePath" => 
        i += 1; var sp = List[Int]()
        while(i < args.length && args(i).forall(_.isDigit)){
          sp ::= args(i).toInt; i += 1
        }
        assert(sp.nonEmpty)
        significancePaths ::= sp.reverse
      case "--checkDeadlock" => checkDeadlock = true; i += 1
      case "--profile" => profiling = true; interval = args(i+1).toInt; i += 2
      case "--profileFlat" =>
        profilingFlat = true; interval = args(i+1).toInt; i += 2
      case "--profileBoth" =>
        profilingBoth = true; interval = args(i+1).toInt; i += 2
      case "--verbose" => verbose = true; i += 1
      case "--bound" => bound = args(i+1).toInt; i += 2
      case "--timing" => timing = true; i += 1
      // case "--memoryless" => memoryless = true; i += 1
      case "--noDebug" => debuggable = false; i += 1
      case "--test" => testing = true; i += 1
      case "-p" => numThreads = args(i+1).toInt; i += 2
      case fn => fname = fn; i += 1
    }

    assert(fname.nonEmpty || testing, "no filename specified")
    if(checkDeadlock && significancePaths.isEmpty){
      println("No significance path specified."); sys.exit
    }

    println("numThreads = "+numThreads)
    // println(s"profilingBoth = $profilingBoth")
    // Initialise Profiler. 
    ox.gavin.profiling.Profiler.setWorkers(numThreads)

    // Profiler
    def filter(frame: StackTraceElement) : Boolean = 
      SamplingProfiler.defaultFilter(frame) && 
        !frame.getClassName.contains("jdk.internal") // &&
        // !frame.getClassName.contains("uk.ac.ox.cs.fdr")
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
    val profiler = 
      new SamplingProfiler(interval = interval, print = printer)

    // Run the check
    val start = java.lang.System.nanoTime
    try{
      def run() = {
        system = new SystemP.System(fname, checkDeadlock, significancePaths)
        // // Create and run the checker
        checker = new Checker(system)
        print("Compiled for "); printTime(java.lang.System.nanoTime-start)
        checker(bound = bound)
      }

      if(testing){ 
        system = new SystemP.System("CSP/test-file.csp", false, List())
        RemapperP.RemapperTest.test
        CombinerP.CombinerTest.test
        // val systemTest = new SystemP.SystemTest(fname); systemTest.test
        SystemP.SystemTest.test(system)
        val checkerTest = new CheckerTest(system); checkerTest.test
      }
      else if(profiling || profilingFlat || profilingBoth) profiler(run()) 
      else run()
      // if(profiler != null) println(profiler.iters)
      val elapsed0 = (java.lang.System.nanoTime - start) // in ns
      if(timing) println(elapsed0)
      else{
        printTime(elapsed0)
        // val elapsed = elapsed0 / 1000000 // in ms
        // if (elapsed >= 100000){
        //   println(elapsed/1000+"s")
        //   if(elapsed >= 1000000) println(elapsed/60000+"min")
        // }
        // else println(elapsed+"ms")
      }
    }
    finally{ if(system != null) system.finalise }
 
    if(!timing) println("goodbye")
    ox.gavin.profiling.Profiler.report 
    println(s"Unification.renameXCount = "+
      printLong(RemapperP.Unification.renameXCount))
    println(s"Remapper.combine2Count = "+
      printLong(RemapperP.Unification.combine2Count))
    println(s"Unification.combineCount = "+
      printLong(RemapperP.Unification.combineCount))
    if(!testing){ // checker is null when testing
      println(s"checker.effectOnCount = "+printLong(checker.effectOnCount))
      println(s"checker.effectOnViaOthersCount = "+
        printLong(checker.effectOnViaOthersCount))
      println(s"checker.effectOnViaTransCount = "+checker.effectOnViaTransCount)
      println(s"checker.effectOnOthersCount = "+
        printLong(checker.effectOnOthersCount))
      println(s"checker.effectOfPreviousTransitionsCount = "+
        checker.effectOfPreviousTransitionsCount)
      println(s"checker.newViewCount = "+printLong(checker.newViewCount))
      println("checker.addedViewCount = "+printLong(checker.addedViewCount))
      // println("checker.changedServersCount = "+
      //   printLong(checker.changedServersCount))
      // println("checker.effectOnRepetition = "+checker.effectOnRepetition)
    }
  }

}
 
 
