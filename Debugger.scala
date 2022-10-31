package ViewAbstraction

import scala.collection.mutable.ArrayBuffer

/** Object to produce debugging output.
  * @param system the system we are debugging.
  * @param sysAbsViews the abstract views encountered during the search.
  * @param initViews the initial views (of size k). */
class Debugger(
  system: SystemP.System, sysAbsViews: ViewSet, initViews: Array[ComponentView]
){
  import Debugger.{pad,pad0,rPad,Sqle,Sqge}
 
  /** Information about a trace found. 
    * For each i in [0..plies),
    * abss(i) [= befores(i) -events(i)-> afters(i) ]= abss(i+1) (modulo symmetry)
    * where plies = events.size; and also abss(plies) [= befores(plies) if the 
    * latter exists.
    */
  private case class TraceInfo(
    abss: ArrayBuffer[ComponentView], befores: ArrayBuffer[Concretization],
    events: ArrayBuffer[EventInt], afters: ArrayBuffer[Concretization])
  {
    val plies = events.size
    assert(abss.size == plies+1 && afters.size == plies &&
      (befores.size == plies || befores.size == plies+1))

    /** Print this trace. */
    def print(toError: Boolean = false) = {
     println()
      println(pad+abss(0))
      if(!befores(0).matches(abss(0))) 
        println(pad0+Sqle+"\n"+rPad("0: ")+befores(0))
      for(i <- 0 until plies){
        println(pad0+"-"+showEvent(events(i))+"->\n"+pad+afters(i))
        if(i+1 < befores.length && afters(i) != befores(i+1)){
          if(! afters(i).matches(abss(i+1))) 
            println(pad0+Sqge+"\n"+pad+abss(i+1))
          if(! befores(i+1).matches(abss(i+1))){
            // Use ">--->" in the last step, as Sqle might be incorrect
            if(i+1 == plies) println(pad0+">--->") else println(pad0+Sqle)
            println(rPad((i+1).toString+": ")+befores(i+1))
          }
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
  def apply(last: ComponentView): Unit = {
    println("debugging "+last+"\n")
    apply1(last, null)
  }

  /** Produce debugging information for target.
    * @param last if non-null, a View to which target contributed, and 
    * that should be included at the end of the trace; last will be null only
    * in the top-level call. */
  def apply1(target: ComponentView, last: Concretization): Unit = {
    // Find trace leading to error state.
    val tr = findTrace(target, last)
    // Print trace
    tr.print(last == null)
    // Interactively get next thing to do
    def help =
      println("Type: a number from 0 to "+tr.plies+
        " to expand the sources of that state;\n"+
        "'u' to go up a level; 's' to list servers; 'q' to quit.")
    var done = false
    while(!done){
      val input = scala.io.StdIn.readLine("> ")
      input match{
        case "q" => println("Goodbye."); sys.exit()
        case "u" => 
          if(last != null) done = true // backtrack up the stack of traces
          else println("Already at the top level.")
        case st if st.nonEmpty && st.forall(_.isDigit) =>
          val n = st.toInt
          // If this is an induced transition, the other view.
          val (pre,cv,cv1) = tr.abss(n+1).preInducedView
          expandConc(tr.befores(n), pre, cv, cv1)
          tr.print(last == null) // re-print trace on return
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
  private def findTrace(target: ComponentView, conc: Concretization = null)
      : TraceInfo = { 
    var v: ComponentView = target
    var done = initViews.contains(v)
    // init records whether we should select penultimate as the source of the
    // next gamma transition.
    // var init = penultimate != null
    // Build up trace in reverse.
    val befores, afters = new ArrayBuffer[Concretization]
    val abss = new ArrayBuffer[ComponentView];
    val events = new ArrayBuffer[EventInt]
    abss += target // IMPROVE: should we have the next Concretization here?
    // Inv: for each i in [0..events.length),
    //        abss(i) [= befores(i) -events(i)-> afters(i) =] abss(i+1)
    // (modulo renaming).  And v = abss.target
    // befores, events, afters have same length; abss is one longer
    while(!done){
      val (pre,e,post) = v.getCreationInfo
      // assert(pre.ply <= v.ply)
      // if(pre.ply > v.ply) 
      //   println("Unexpected ply in pre: $pre $pre.ply$; $v $v.ply$")
      assert(e >= 0, s"$pre -($e)-> $post")
      befores += pre; events += e; afters += post
      // Note: the "head" below is somewhat arbitrary.  The debugger allows
      // expansion of other views.
      val v1 = RemapperP.Remapper.remapView(pre.toComponentView.head)
      try{ v = sysAbsViews.get(v1) }
      catch{
        case e: java.lang.AssertionError =>
          e.printStackTrace()
          println("pre = $pre\n"+pre.toComponentView+
            "\nabss =\n"+abss.mkString("\n")+
            "\nevents =\n"+events.map(showEvent).mkString("\n")+
            "\nbefores =\n"+befores.mkString("\n")+
            "\nafters =\n"+afters.mkString("\n") )
          abss += v1
          val beforesR = befores.reverse; if(conc != null) beforesR += conc
          val ti = 
            TraceInfo(abss.reverse, beforesR, events.reverse, afters.reverse)
          ti.print(false); sys.exit()
      } // end of catch
      abss += v
      done = initViews.contains(v)
    }
    if(verbose) println()
    // Add conc at end if appropriate
    val beforesR = befores.reverse; if(conc != null) beforesR += conc
    TraceInfo(abss.reverse, beforesR, events.reverse, afters.reverse)
  }

  /** Expand the concretization conc, giving the trace leading to the secondary
    * view.  If pre != null, then conc was formed to capture an induced
    * transition, with a transition starting with pre on view cv1, where cv is
    * the normal form of cv. */
  private def expandConc(conc: Concretization, 
    pre: Concretization, cv: ComponentView, cv1: ComponentView)
  = {
    val secondary = conc.getSecondaryView; val rv = conc.getReferencingViews
    println(s"Secondary view = $secondary")
    println(s"Referencing views = "+
      (if(rv == null) "null" 
      else rv.filter(_ != null).map(_.toString).mkString("; ")))
    if(pre != null){
      println(s"Transition from $pre\nacting on $cv")
      if(cv != cv1) println(s"       == $cv1")
    }
    // Get the options for expanding
    val options = new ArrayBuffer[ComponentView]
    /* Add to options, avoiding repetitions. */
    def maybeAdd(cv: ComponentView) = if(!options.contains(cv)) options += cv
    def maybeAddList(cvs: Seq[ComponentView]) = for(cv <- cvs) maybeAdd(cv)

    // All views of conc.  This repeats a view seen in the previous expansion.
    maybeAddList(conc.toComponentView) // options ++= conc.toComponentView
    if(secondary != null) maybeAdd(secondary) // options += secondary
    if(pre != null){
      maybeAdd(cv) // options += cv
      val servers = pre.servers; assert(cv.servers == servers)
      val preCpts = pre.components; val cpts1 = cv1.components
      val prePrinc = preCpts(0)

// FIXME: below only when singleRef
      // Find the missing views required for condition (b). 
      // val crossRefs =
      //   EffectOn.getCrossRefs(servers, cv1.components, pre.components)
      // println("crossRefs = "+crossRefs.map(StateArray.show))
      val missing: List[ComponentView] =
        SingleRefEffectOn.getCrossRefs(servers, cpts1, preCpts)
          .map(new ComponentView(servers, _))
      if(missing.isEmpty) println("No cross reference views.")
      else{
        println(s"Cross reference views: "+missing.mkString(",\n  "))
        maybeAddList(missing) // options ++= missing
      }

      // Find the missing views required for condition (c).
      // Identities of common missing components
      val commonMissing = 
        SingleRefEffectOnUnification.commonMissingRefs(cpts1, preCpts)
      if(commonMissing.isEmpty) println("No common missing references.")
      else{
        println(s"Common missing component identities: "+
          commonMissing.map(getScriptName).mkString(", "))
        for(pid <- commonMissing){
          // All states instantiating pid compatible with pre.  Note, using
          // cpts1(0) here would be wrong, since it's not in normal form.
          val insts =
            MissingCommon.allInstantiations(servers, prePrinc, pid, sysAbsViews)
          // println("Possible states for "+getScriptName(pid)+
          //   s" with $prePrinc: "+insts.mkString(", "))
          for(c <- insts){
            val req = MissingCommon.requiredCpts(servers, preCpts, cpts1, c)
            if(req.forall(cpts => sysAbsViews.contains(servers, cpts))){
              val req1 = Array(prePrinc, c) :: req.toList
              println(s"Required views for $c: "+
                req1.map(StateArray.show).mkString(",\n  "))
              // println("  all found")
              maybeAddList(req1.map(new ComponentView(servers, _)))
            }
          }
        }
      }
    }
    if(rv != null) for(v <- rv; if v != null) maybeAdd(v) // options += v
    // Prompt the user for the option to explore. 
    val len = options.length
    if(len == 0) println(s"No secondary components found in $conc")
    else{
      for(i <- 0 until len) println(s"$i. ${options(i)}")
      var done = false
      def help = 
        println(s"Type: a number from 0 to ${len-1} to expand that view;\n"+
          "'u' to go up a level; or 'q' to quit.")
      while(!done){
        val input = scala.io.StdIn.readLine("> ")
        if(input.nonEmpty && input.forall(_.isDigit)){
          val n = input.toInt
          if(0 <= n && n < len){ 
            apply1(sysAbsViews.get(options(n)), conc); done = true 
          }
          else help
        }
        else if(input == "u") done = true
        else if(input == "q") { println("Goodbye."); sys.exit() }
        else help
      }
    }
  }

  /** The script name for pId. */
  private def getScriptName(pId: ProcessIdentity) = scriptNames(pId._1)(pId._2)

  /** Print the server names. */
  private def showServers = {
    val serverNames = system.serverNames
    for(i <- 0 until serverNames.length) println(rPad(s"$i: ")+serverNames(i))
  }

}

// ==================================================================

object Debugger{

  // Parameters used in printing: indent is the width of the left-hand column;
  // pad is a blank left-hand column.
  private val indent = 7; private val pad0 = " "*(indent-3);
  private val pad = " "*indent
  /** Right pad st to the width of the left-hand column. */
  def rPad(st: String) = st.padTo(indent, ' ')

  // Sub-view symbols
  private val Sqle = '\u2291' // ⊑
  private val Sqge = '\u2292' // ⊒

}
