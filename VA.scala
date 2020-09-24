package ViewAbstraction

// import ox.cads.util.{SamplingProfiler,ProfilerSummaryTree}
import ox.gavin.profiling.{SamplingProfiler,ProfilerSummaryTree}


object VA{ 
  /** Model of the system. */
  var system: System = null // public for profiling

  /** The abstract shapes to use. */
  // private var aShapes = List[Shape]()

  // /** The size of abstractions. */
  // private var k = -1

  /** The checker. */
  var checker: Checker = null

  // /** Create the shapes of abstractions (defining them if necessary).  Check
  //   * correctness, in particular convexity.  Pre: system has been
  //   * initialised. */
  // private def checkAShapes() = {
  //   if(k < 0){
  //     if(aShapes.isEmpty){
  //       println("No abstraction shapes specified."); sys.exit
  //     }
  //     else k = aShapes(0).sum
  //   }
  //   else if(aShapes.isEmpty){
  //     if(numFamilies == 1) aShapes = List(Array(k))
  //     else{
  //       assert(numFamilies == 2, numFamilies) // FIXME
  //       aShapes = (for(i <- 0 to k) yield Array(i,k-i)).toList
  //     }
  //   }
  //   println("aShapes = "+aShapes.map(_.mkString("<", ",", ">")))

  //   // Check aShapes ok
  //   if(!aShapes.forall(sh => sh.length == numFamilies && sh.sum == k)){
  //     val badShapes =
  //       aShapes.filter(sh => sh.length != numFamilies || sh.sum != k)
  //     println("Illegal abstract shapes: "+
  //               badShapes.map(_.mkString("<", ",", ">"))+
  //               ".\nnumFamilies = "+numFamilies)
  //     sys.exit
  //   }

  //   // Check (geometric) convexity
  //   if(numFamilies > 1){
  //     assert(numFamilies == 2) // FIXME
  //     val mins = Array.tabulate(numFamilies)(i => aShapes.map(_(i)).min)
  //     val maxs = Array.tabulate(numFamilies)(i => aShapes.map(_(i)).max)
  //     for(i <- mins(0) to maxs(0)){
  //       val sh1 = Array(i,k-i)
  //       if(! aShapes.exists(_.sameElements(sh1))){
  //         println("Abstract shapes not convex: needs shape "+
  //                   sh1.mkString(" "))
  //         sys.exit
  //       }
  //     }
  //   }
  // }

  // /** Create the shapes of concretizations. */
  // private def makeCShapes: List[Shape] = {
  //   // Size of concretizations.
  //   val l = if(system.threeWaySyncFound) k+2 else k+1
  //   println("Using l = "+l)

  //   // calculate the concrete shapes
  //   val cShapes: List[Array[Int]] =
  //     if(numFamilies == 1) List(Array(l))
  //     else{
  //       assert(numFamilies == 2) // FIXME
  //       if(l == k+1) (
  //         ( for(sh <- aShapes) yield List( sh(0)+1, sh(1) ) ) ++
  //           ( for(sh <- aShapes) yield List( sh(0), sh(1)+1 ) )
  //       ).distinct.map(_.toArray)
  //       else{
  //         // calculate cShapes based on three-way synchronisations
  //         // between distinct types of components.
  //         val c1 =
  //           for(f1 <- 0 until numFamilies; f2 <- 0 to f1;
  //               if system.threeWaySyncs(f1)(f2); sh <- aShapes) yield{
  //             val sh1 = sh.clone; sh1(f1) += 1; sh1(f2) += 1; sh1
  //           }
  //         // Add 2 to any family not involved in a three-way sync
  //         val c2 =
  //           for(f1 <- 0 until numFamilies;
  //               if (0 to f1).forall(f2 => !system.threeWaySyncs(f1)(f2)) &&
  //               (f1+1 until numFamilies).forall(f2 =>
  //                 !system.threeWaySyncs(f2)(f1));
  //               sh <- aShapes) yield{
  //             println("Creating concretizations by adding two components of family"+f1)
  //             val sh1 = sh.clone; sh1(f1) += 2; sh1
  //           }
  //         // Note: above not really tested.
  //         // Remove duplicates
  //         (c1++c2).foldRight(List[Shape]())((sh,shs) =>
  //           if(shs.exists(sh1 => sh1.sameElements(sh))) shs else sh::shs)
  //         // Note: removing of duplicates not really tested
  //       }
  //     }
  //   // if(l == k+1) (for(i <- 0 to k+1) yield Array(i,k+1-i)).toList
  //   // else (for(i <- 1 to k+1) yield Array(i,k+2-i)).toList
  //   assert(cShapes.forall(sh => sh.length == numFamilies && sh.sum == l))
  //   println("cShapes = "+cShapes.map(_.mkString("<", ",", ">")))
  //   Remapper.mkIndexPerms(cShapes.map(_.max).max)
  //   Views.setPoolSize(cShapes)
  //   cShapes
  // }

  /** Run a check.  Called by ScalaInstrumentation. */
  def check(fname: String, bound: Int,
            checkDeadlock: Boolean, significancePaths: List[SignificancePath],
            verbose: Boolean) 
      : Unit = {
    // assert(k == k1 && aShapes == aShapes1)
    // k = k1; aShapes = aShapes1
    // val start = java.lang.System.nanoTime
    system = new System(fname, checkDeadlock, significancePaths)

  //   checkAShapes
  //   // Set cShapes
  //   val cShapes: List[Array[Int]] = makeCShapes
  //   system.setCShapes(cShapes)
  //   Views.makeCombinations(cShapes.map(_.max).max)

    // Create and run the checker
    println("Created system")
    checker = new Checker(system)
    checker(bound = bound, verbose = verbose)
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
    var verbose = false; var bound = Int.MaxValue; var timing = false

    while(i < args.length) args(i) match{
      // case "-k" => k = args(i+1).toInt; i += 2
      // case "--shape" =>
      //   // Get the next shape from the command line
      //   i += 1; var shape = List[Int]()
      //   while(i < args.length && args(i).forall(_.isDigit)){
      //     shape ::= args(i).toInt; i += 1
      //   }
      //   // println("shape "+shape)
      //   aShapes ::= shape.reverse.toArray
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
      case "--verbose" => verbose = true; i += 1
      case "--bound" => bound = args(i+1).toInt; i += 2
      case "--timing" => timing = true; i += 1
      case "--memoryless" => memoryless = true; i += 1
      // case "--oldStyle" => oldStyle = true; newStyle = false; i += 1
      case "--noDebug" => debuggable = false; i += 1
      case "-p" => numThreads = args(i+1).toInt; i += 2
      case fn => fname = fn; i += 1
    }

    assert(fname.nonEmpty, "no filename specified")
    if(checkDeadlock && significancePaths.isEmpty){
      println("No significance path specified."); sys.exit
    }

    println("numThreads = "+numThreads)
    // Initialise Profiler.  FIXME
    ox.gavin.profiling.Profiler.setWorkers(numThreads)

    // Profiler
    def filter(frame: StackTraceElement) : Boolean = 
      SamplingProfiler.defaultFilter(frame) && 
        !frame.getClassName.contains("jdk.internal") // &&
        // !frame.getClassName.contains("uk.ac.ox.cs.fdr")
    val printer =
      if(!profilingFlat)
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
        // check(fname, k, aShapes, bound, 
        //       checkDeadlock, significancePaths, verbose)
        system = new System(fname, checkDeadlock, significancePaths)
        // checkAShapes
        // // Set cShapes
        // val cShapes: List[Array[Int]] = makeCShapes
        // system.setCShapes(cShapes)
        // Views.makeCombinations(cShapes.map(_.max).max)
        // // Create and run the checker
        checker = new Checker(system)
        print("Compiled for "); printTime(java.lang.System.nanoTime-start)
        checker(bound = bound, verbose = verbose)
      }

      if(profiling || profilingFlat) profiler(run()) else run()
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
  }

}
 
 
