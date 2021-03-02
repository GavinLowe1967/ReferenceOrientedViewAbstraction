package ViewAbstraction

import scala.collection.mutable.ArrayBuffer

/** Object to produce debugging output.
  * @param system the system we are debugging.
  * @param k the abstraction parameter used.
  * @param l the length of concrete views.
  * @param aShapes the shapes of abstract views
  * @param sysAbsViews the abstract views encountered during the search.
  * @param initViews the initial views (of size k). */
class Debugger(
  system: SystemP.System, sysAbsViews: ViewSet, initViews: Array[View]
){

  // Parameters used in printing: indent is the width of the left-hand column;
  // pad is a blank left-hand column.
  private val indent = 7; private val pad0 = " "*(indent-3);
  private val pad = " "*indent
  /** Right pad st to the width of the left-hand column. */
  def rPad(st: String) = st.padTo(indent, ' ')
 
  /** Information about a trace found. 
    * For each i in [0..plies),
    * abss(i) [= befores(i) -events(i)-> afters(i) ]= abss(i+1) (modulo symmetry)
    * where plies = events.size; and also abss(plies) [= befores(plies) if the 
    * latter exists.
    */
  private case class TraceInfo(
    abss: ArrayBuffer[View], befores: ArrayBuffer[Concretization],
    events: ArrayBuffer[EventInt], afters: ArrayBuffer[Concretization])
  {
    val plies = events.size
    assert(abss.size == plies+1 && afters.size == plies &&
      (befores.size == plies || befores.size == plies+1))

    private val Sqle = '\u2291' // ⊑
    private val Sqge = '\u2292' // ⊒

    /** Print this trace. */
    def print(toError: Boolean = false) = {
     println
      println(pad+abss(0))
      if(!befores(0).matches(abss(0))) 
        println(pad0+Sqle+"\n"+rPad("0: ")+befores(0))
      for(i <- 0 until plies){
        println(pad0+"-"+system.showEvent(events(i))+"->\n"+pad+afters(i))
        if(i+1 < befores.length && afters(i) != befores(i+1)){
          if(! afters(i).matches(abss(i+1))) 
            println(pad0+Sqge+"\n"+pad+abss(i+1))
          if(! befores(i+1).matches(abss(i+1)))
            println(pad0+Sqle+"\n"+rPad((i+1).toString+": ")+befores(i+1))
        }
      }
      if(toError){
        assert(befores.size == plies); println(pad0+"-error->")
      }
    }
  } // end of TraceInfo

  /* ============================================ */

  /** Produce debugging information for last.
    * @param plies the number of plies in the search, i.e. the number of events
    * that happened before the state last was reached. */
  def apply(last: View): Unit = {
    println("debugging "+last+"\n")
    apply1(last, null)
  }

  /** Produce debugging information for last.
    * @param penultimate if non-null, a View of size k+1 that contributed
    * to last, and that should be included in the trace; penultimate will be
    * null only in the top-level call. */
  def apply1(last: View, penultimate: Concretization): Unit = {
    // Find trace leading to error state.
    val tr = findTrace(last, penultimate)
    // Print trace
    tr.print(penultimate == null)
    // Interactively get next thing to do
    def help =
      println(
        "Type: a number from 0 to "+tr.plies+
          " to expand the sources of that state;\n"+
          "'u' to go up a level; 's' to list servers; 'q' to quit.")
    var done = false
    while(!done){
      val input = scala.io.StdIn.readLine("> ")
      input match{
        case "q" => println("Goodbye."); sys.exit
        case "u" => 
          if(penultimate != null) done = true // backtrack up the stack of traces
          else println("Already at the top level.")
        case st if st.nonEmpty && st.forall(_.isDigit) =>
          expandConc(tr.befores(st.toInt))
          tr.print(penultimate == null) // re-print trace on return
        case "s" => showServers
        case "h" | "?" | "help" => help
        case _ => println("Invalid command."); help
      }
    }
  }

  // Flag to make findTrace print information during the backwards search
  private val verbose = true

  /** Find the trace leading to target. 
    * @param conc if non-null, a concretization, which is an extension 
    * of target, and that should be included in the trace. */
  private def findTrace(target: View, conc: Concretization = null)
      : TraceInfo = { 
    var v: View = target
    var done = initViews.contains(v)
    // init records whether we should select penultimate as the source of the
    // next gamma transition.
    // var init = penultimate != null
    // Build up trace in reverse.
    val befores, afters = new ArrayBuffer[Concretization]
    val abss = new ArrayBuffer[View];
    val events = new ArrayBuffer[EventInt]
    abss += target // IMPROVE: should we have the next Concretization here?
    // Inv: for each i in [0..events.length),
    //        abss(i) [= befores(i) -events(i)-> afters(i) =] abss(i+1)
    // (modulo renaming).  And v = abss.target
    // befores, events, afters have same length; abss is one longer
    while(!done){
      val pre = v.pre; val e = v.e; val post = v.post
      assert(e >= 0, s"$pre -($e)-> $post")
      // println(s"$pre -${system.showEvent(e)}-> $post ]= $v")
      befores += pre; events += e; afters += post
      v = sysAbsViews.getRepresentative(pre.toComponentView); abss += v
      done = initViews.contains(v)
    }
    if(verbose) println
    // Add conc at end if appropriate
    val beforesR = befores.reverse; if(conc != null) beforesR += conc
    TraceInfo(abss.reverse, beforesR, events.reverse, afters.reverse)
  }

  /** Expand the concretization conc, giving the trace leading to the secondary
    * view. */
  private def expandConc(conc: Concretization) = {
    val cv = conc.getSecondaryView
    println(s"Secondary view = $cv")
    if(cv == null) println(s"No secondary components found in $conc")
    else apply1(cv, conc)
  }

  /** Print the server names. */
  private def showServers = {
    val serverNames = system.serverNames
    for(i <- 0 until serverNames.length) println(rPad(s"$i: ")+serverNames(i))
  }

}


// ============================================================================

      // before was created by gamma using the elements of absList
    //   val absList =
    //     if(init) { init = false; List(penultimate) }
    //     else
    //       Views.alpha(aShapes, before.componentView).map(absCpts =>
    //         View.mkView(before.servers, absCpts))
    //   // after =alpha=> abs1 == abs =gamma=> before, and this is the latest
    //   // contributor to before to be found.
    //   val (abs,abs1,after,ply) = absList.map(getStep).maxBy(_._4)
    //   // val abs =
    //   //   if(init) { init = false; penultimate }
    //   //   else{
    //   //     val absCpts = Views.alpha(k, aShapes, before.componentView).head
    //   //     system.mkView(before.servers, absCpts)
    //   //   }
    //   abss += abs
    //   // val (abs1,after,ply) = getStep(abs)
    //   if(ply < 0) done = true
    //   // if(initViews.contains(abs1)) done = true
    //   else{
    //     abs1s += abs1
    //     // prev1 was created by alpha from prev2
    //     //val (after,_) = View.alphaLog(abs1)
    //     //if(verbose) println("<-alpha=\n"+after)
    //     afters += after 

    //     // The checker found the transition before -e-> after
    //     val (b, e) = after.getPred; before = b
    //     // val (b, e) = system.debugLog(after); before = b
    //     // assert(after.getPred == (b,e))
    //     assert(before.componentView.length == l)
    //     // assert(checkLength(before.componentView, 1))
    //     if(verbose) println("<-"+system.showEvent(e)+"-\n"+before)
    //     befores += before; events += e 
    //   }
    // // end of while(done)

  /** Given an abstraction abs, return (abs, abs1, after, ply) such that on ply
    * ply, after =alpha=> abs1 equiv abs. */
  // def getStep(abs: View): (View, View, View, Int) = {
  //   assert(abs.componentView.length == k)
  //   if(verbose) println("<=gamma=\n"+abs)
  //   // abs1 is equivalent to abs in sysAbsViews.
  //   val abs1 = sysAbsViews.getRepresentative(abs)
  //   assert(abs1 == abs) // but they will be different objects
  //   if(initViews.contains(abs1)) (abs, abs1, null, -1)
  //   else{
  //     // val (after,ply) = View.alphaLog(abs1)
  //     // assert(abs1.getPred == (after,ply))
  //     val (after,ply) = abs1.getPred
  //     if(verbose) println("<-alpha=\n"+after)
  //     (abs, abs1, after, ply)
  //   }
  // }



  /** Show all Views of size k that contributed to conc (of size l). */
  // private def expandGamma(conc: View) = {
  //   val cmpts = conc.componentView
  //   assert(cmpts.length == l)
  //   // assert(checkLength(cmpts, 1))
  //   println("Expanding "+conc)
  //   // The abstract views of the components
  //   val absViews = Views.alpha(aShapes, cmpts)
  //   // (for(i <- 0 until k+1) yield cmpts.take(i)++cmpts.drop(i+1)).toList
  //   // Create all abstract system views from these
  //   val abss: List[View] =
  //     absViews.map(View.mkView(conc.servers, _))
  //   def printAbss = for(i <- 0 until abss.length) println(rPad(s"$i: ")+abss(i))
  //   printAbss
  //   // Interactively get next thing to do
  //   def help =
  //     println(
  //       "Type: a number from 0 to "+(abss.length-1)+
  //         " to obtain the trace leading to that state;\n"+
  //         "'u' to go up a level; 's' to list servers; 'q' to quit.")
  //   var done = false
  //   while(!done){
  //     val input = scala.io.StdIn.readLine("> ")
  //     input match{
  //       case "q" => println("Goodbye."); sys.exit
  //       case "u" => done = true // backtrack up the stack of traces
  //       case st if st.nonEmpty && st.forall(_.isDigit) =>
  //         apply1(conc, abss(st.toInt))
  //         printAbss // re-print choices on return
  //       case "s" => showServers
  //       case "h" | "?" | "help" => help
  //       case _ => println("Invalid command."); help
  //     }
  //   }
  // }

  /* IMPROVE: The debugging needs to be improved.  Try to find consecutive
   * alpha/gamma steps to minimise the change, i.e. either giving the same
   * view or one that is equivalent, if possible. */

