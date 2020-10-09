package ViewAbstraction

import scala.collection.mutable.ArrayBuffer
import java.util.concurrent.atomic.{AtomicLong,AtomicInteger,AtomicBoolean}

/** A checker for the view abstraction algorithm, applied to system.
  * @param aShapes the shapes of abstractions.
  * @param cShapes the shapes of concretizations. */
class Checker(system: System)
{
  /** The abstract views. */
  var sysAbsViews: ViewSet = null

  val Million = 1000000

  private var done = new AtomicBoolean(false); private var ply = 1

  /** The new views to be considered on the next ply. */
  private var nextNewViews: ArrayBuffer[View] = null

  /** An extended transition represents the pre- and post-states of a
    * transition, and extends a View by adding in the states of any additional
    * components that synchronise on the transition, and any components to
    * which the principal component obtains a reference. */
  private type ExtendedTransition = (Concretization, Concretization)

  /** The extended transitions found so far.  Abstractly, a set of
    * ExtendedTransitions. */
  private val transitions: TransitionSet = new SimpleTransitionSet

  /** A TransitionTemplate (pre, post, id, oe) represents an extended transition
    * pre U st --> post U st' for every state st and st' such that (1) st and
    * st' have identity id; (2) st is compatible with pre; (3) if oe = Some(e)
    * then st -e-> st', otherwise st = st'.  */
  private type TransitionTemplate = TransitionTemplateSet.TransitionTemplate
  // (Concretization, Concretization, ProcessIdentity, Option[EventInt])

  private val transitionTemplates: TransitionTemplateSet = 
    new SimpleTransitionTemplateSet

  /** Add v to  sysAbsViews, and nextNewViews if new. */
  @inline private def addView(v: View): Boolean = {
    if(sysAbsViews.add(v)){ nextNewViews += v; true }
    else false
  }

  /** Add the principal component view of conc to sysAbsViews, and nextNewViews
    * if new. */
  @inline private def addViewFromConc(conc: Concretization) = {
    val v = Remapper.remapComponentView(conc.toComponentView)
    if(addView(v)) println(s"$v.  ***Added***") 
    // else false // println(s"$v.  Already present.")
  }
// FIXME: should we be extracting other views here?

  /** Store the ExtendedTransition pre -> post, and calculate its effect on
    * previously found views. */
  @inline private def addTransition(pre: Concretization, post: Concretization) 
  = {
    transitions.add(pre, post); effectOnOthers(pre, post)
  }

  // ========= Processing a single view

  /** Process v, calculating all the concrete transitions from v, adding the
    * post-states to sysAbsViews, and adding new ones to nextNewViews.
    */
  private def process(v: View) = { 
    println(s"\nProcessing $v")
    v match{
      case cv: ComponentView =>
        for((pre, e, post, outsidePids) <- system.transitions(cv)){ 
          // FIXME: not all transitions included yet
          println(s"\n$pre -${system.showEvent(e)}-> $post ["+
            outsidePids.map(State.showProcessId)+"]")
          assert(pre.components(0) == cv.principal)
          // Find new views as a result of this transition
          processTransition(pre, e, post, outsidePids)
        } // end of for((pre, e, post, outsidePids) <- trans)
        // Effect of previous transitions on this view
        effectOfPreviousTransitions(cv)
        effectOfPreviousTransitionTemplates(cv)
    }
  } 

  // ========= Processing a transition from a view.

  /** Process the transition pre -e-> post, creating the corresponding new views
    * and adding them to sysAbsViews and nextNewViews.  Add appropriate
    * TransitionTemplates and ExtendedTransitions to transitionTemplates and
    * transitions, respectively.
    * @param outsidePids the identities of components outside pre that 
    * synchronise on the transition. */
  @inline private def processTransition(
    pre: Concretization, e: EventInt, post: Concretization, 
    outsidePids: List[ProcessIdentity]) 
  = {
    val princ1 = post.components(0)
    // Process ids of other components
    val otherIds = pre.components.tail.map(_.componentProcessIdentity)
    assert(post.components.map(_.componentProcessIdentity).sameElements(
      pre.components.map(_.componentProcessIdentity)))
    // newPids is the components to which the principal component gains
    // references but that are outside pre/post.
    val newPids: Array[ProcessIdentity] =
      princ1.processIdentities.tail.filter(p =>
        !isDistinguished(p._2) && !otherIds.contains(p))
    // The following assertion (outsidePids subset of newPids) captures an
    // assumption that the principal component cannot acquire a reference from
    // nowhere: the reference must be acquired either from another process in
    // the view or by synchronising with that other component.
    assert(outsidePids.forall(pid => newPids.contains(pid)))
    // if(newPids.nonEmpty)
    //   println(s"newPids = "+newPids.map(State.showProcessId).mkString(","))

    if(newPids.isEmpty){
      // Case 1: no new nondistinguished parameter
      assert(outsidePids.isEmpty) // FIXME (simplifying assumption)
      addViewFromConc(post)
      // Store this transition, and calculate effect on other views.
      addTransition(pre, post)
    }
    else{ // Case 2: one new parameter from outside the view
      assert(newPids.length == 1 && outsidePids.length <= 1)
      // FIXME (simplification)
      val newPid = newPids.head
      // Find all states for newPid, consistent with pre, that can perform e if
      // in outsidePids, and their subsequent states (optionally after e).
      val oe = if(outsidePids.nonEmpty) Some(e) else None
      // Store transition template
      transitionTemplates.add(pre, post, newPid, oe)
      // Get extended transitions based on this
      instantiateTransitionTemplate(pre, post, newPid, oe)
    } // end of else
  }


  // ========= Extending TransitionTemplates 

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, oe) based on prior views.
    * @return all such ExtendedTransitions. 
    * Called from processTransition. */
  private def instantiateTransitionTemplate(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, oe: Option[EventInt]) 
  = {
    val servers = pre.servers
    for(v1 <- sysAbsViews.toArray) v1 match{ // IMPROVE iteration
      case cv: ComponentView =>
        if(cv.servers == servers)
          instantiateTransitionTemplateBy(pre, post, newPid, oe, cv)
    } // end of for ... match
    // result
  }

  /** The effect of view cv on previous TransitionTemplates.
    *  Called from process. */
  private def effectOfPreviousTransitionTemplates(cv: ComponentView) = {
    for((pre, post, id, oe) <- transitionTemplates.iterator){
      if(pre.servers == cv.servers)
        instantiateTransitionTemplateBy(pre, post, id, oe, cv)
    }
  }

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, oe) and the view cv.  For each, store the transition, the
    * post-state, and calculate the effect on other views.
    * Called from instantiateTransitionTemplate and 
    * effectOfPreviousTransitionTemplates. */
  @inline private def instantiateTransitionTemplateBy(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, oe: Option[EventInt], cv: ComponentView)
  = {
    require(pre.servers == cv.servers)
    val extenders = system.consistentStates(newPid, pre, oe, cv)
    for((outsideSt, outsidePosts) <- extenders){
      assert(outsidePosts.nonEmpty)
      if(isExtendable(pre, outsideSt)){
        val extendedPre = pre.extend(outsideSt)
        for(postSt <- outsidePosts){
          val extendedPost = post.extend(postSt)
          println(s"Extended transition from template $extendedPre -"+
            (oe match{ case Some(e) => system.showEvent(e); case None => ""})+
            s"-> $extendedPost")
          addViewFromConc(extendedPost)
          // Store this transition, and calculate effect on other views.
          addTransition(extendedPre, extendedPost)
        }
      }
      else println(s"$outsideSt not compatible with earlier views")
    } // end of for((outsideSt, outsidePosts) <- ...)
  }

  /** Is conc extendable by state st, given the current set of views?  For each
    * cpt component of conc U st, is there a view in SysAbsViews with cpt as
    * the principal component and agreeing on all common processes. 

    * PRE: conc is compatible with SysAbsViews, and conc does not include
    * st.identity.  This means it is enough to check the condition for cpt =
    * st or a non-principal component of conc that references st. ??????
    */
  @inline private def isExtendable(conc: Concretization, st: State): Boolean = {
    require(sysAbsViews.contains(conc.toComponentView))
    // Also every other state in conc is compatible FIXME CHECK
    // require(conc.components.forall(
    //   _.componentProcessIdentity != st.componentProcessIdentity))
    // Rename st to make it canonical with servers
    val servers = conc.servers; val components = conc.components
    val map = Remapper.createMap(servers.rhoS)
    val nextArg = Remapper.createNextArgMap(servers.rhoS)
    var st1 = Remapper.remapState(map, nextArg, st) // this seems wrong *** 
    val id1 = st1.componentProcessIdentity
    require(components.forall(_.componentProcessIdentity != id1))
    println(s"isExtendable($conc, $st) renamed to $st1")

    // Test whether there is an existing view with a renaming of st as
    // principal component, and the same servers as conc.  IMPROVE: iteration
    val viewsArray = sysAbsViews.toArray
    var i = 0; var found = false
    while(i < viewsArray.length && !found) viewsArray(i) match{
      case cv1: ComponentView =>
        if(cv1.servers == servers && cv1.principal == st1){
// FIXME: need to check rest of components are compatible.  At present this is
// safe, but maybe giving too many matches.  Gives an extension[12[1](T0,N0)
// || 7[0](N0,N1) || 6[0](N1)] from where initNode.T0.N1.A.N0 performed.
          found = true
        }
        i += 1
    } // end of while ... match

    if(found){
      // If any component cpt of conc references st, then search for a
      // suitable view with a renaming of cpt and st.
      val id = st.componentProcessIdentity
      // Test whether any component of conc references st
      var j = 0; val length = components.length
      while(j < length && found){
        val cpt = components(j)
        if(cpt.processIdentities.contains(id)){
          println(s"isExtendable($conc) with reference to $st")
          found = containsXXX(conc, st1, j) // || true // FIXME
        }
        j += 1
      }
    }
    found    
  }

  /** Does sysAbsViews contain a view corresponding to component j's view of
    * conc and st?  Pre: component j references st. */
  private def containsXXX(conc: Concretization, st: State, j : Int): Boolean = {
    println(s"containsXXX($conc, $st, $j)")
    val pCpt = conc.components(j)
    // Rename pCpt to be principal component
    val servers = conc.servers; val rhoS = servers.rhoS
    val map = Remapper.createMap(rhoS)
    val nextArg = Remapper.createNextArgMap(rhoS)
    val pCptR = Remapper.remapState(map, nextArg, pCpt)
    println(s"$pCpt renamed to $pCptR") // TEST: find case where not identity
    // Find index in cpt of reference to st, and hence what st.id gets renamed to
    val stId = st.id
    val k = pCpt.ids.indexOf(stId); assert(k > 0)
    val stIdR = pCptR.ids(k)
    println(s"$st identity renamed to "+State.showProcessId((st.family, stIdR)))
    val cs1 = st.cs    
    
    // Test whether sysAbsViews contains a view matching servers, with cptR as
    // the principal component, and containing a component with identity idR
    // in control state cs1.
    // FIXME: need to check rest also compatible with conc.
    val viewsArray = sysAbsViews.toArray; var i = 0; var found = false
    while(i < viewsArray.length && !found) viewsArray(i) match{
      case cv1: ComponentView =>
        if(cv1.servers == servers && cv1.principal == pCptR &&
          cv1.components.exists(cpt1 => cpt1.cs == cs1 && cpt1.id == stIdR) ){
          println(s"found match with $cv1"); found = true; ???
// FIXME: I'm very unsure about this.
        }
        i += 1
    }
    found
  }


  // ========= Effect of transitions on other views

  /** Effect on other views of a transition pre -> post.  For every view v1 in
    * sysAbsViews, if it is consistent with pre (i.e. unifiable), and contains
    * at least one process that changes state, then update as per this
    * transition. */
  private def effectOnOthers(pre: Concretization, post: Concretization) = {
    // println(s"effectOnOthers($pre, $post)")
    for(v1 <- sysAbsViews.toArray) v1 match{ // IMPROVE iteration
      case cv: ComponentView  =>
        if(cv.servers == pre.servers){
          // println(s"Effect on $cv");
          // IMPROVE if nothing changed state.
          effectOn(pre, post, cv)
        }
    } // end of match
  }
  // IMPROVE: need better way of iterating over ViewSet

  /** The effect of the transition pre -> post on cv.  If cv is consistent with
    * pre (i.e. unifiable), and contains at least one process that changes
    * state, then update as per this transition.  Generate all new views that
    * would result from this view under the transition.  Called by
    * effectOnOthers and effectOfPreviousTransitions.  */
  private def effectOn(
    pre: Concretization, post: Concretization, cv: ComponentView)
  = {
    println(s"effectOn($pre, $post, $cv)")
    require(pre.servers == cv.servers)
    val newCpts = Remapper.combine(pre, cv)
    for((cpts, unifs) <- newCpts){
      // println("cpts = "+cpts.mkString("[",",","]")+s"; unifs = $unifs")
      // Find the component of cpts with process identity pid, or return
      // null if no such.
      def find0(pid: ProcessIdentity, cpts: Array[State]): State = {
        var i = 0; var done = false
        while(i < cpts.length && !done){
          if(cpts(i).componentProcessIdentity == pid) done = true else i += 1
        }
        if(done) cpts(i) else null
      }
      // Find the component of post or cpts with process identity pid
      def find(pid: ProcessIdentity): State = {
        val st1 = find0(pid, post.components)
        if(st1 != null) st1
        else{
          val st2 = find0(pid, cpts)
          assert(st2 != null, s"Not found identity $pid in $post or "+
            cpts.mkString("[",",","]"))
          st2
        }
      }
      // Find what cpts(0) gets mapped to by unifs
      val matches = unifs.filter(_._2 == 0)
      val newPrinc =
        if(matches.isEmpty) cpts(0)
        else{assert(matches.length == 1); post.components(matches.head._1)}
      val others = newPrinc.processIdentities.tail.
        filter{case(f,id) => !isDistinguished(id)}.map(find(_))
      val nv = Remapper.remapComponentView(
        new ComponentView(post.servers, newPrinc, others) )
      if(addView(nv))
        println(s"Effect of $pre -> $post\n  on $cv:  -> $nv.  ***Added***")
    }
  }

  /** The effect of previously found extended transitions on the view cv. */
  private def effectOfPreviousTransitions(cv: ComponentView) = {
    // println(s"effectOfPreviousTransitions($cv)")
    for((pre,post) <- transitions.iterator){
      // println(s"considering transition $pre -> $post")
      if(pre.servers == cv.servers) effectOn(pre, post, cv)
    }
  }

  // ========= Main function

  /** Run the checker. 
    * @param bound the number of plys to explore (with negative values meaning 
    * effectively infinite).  */
  def apply(bound: Int = Int.MaxValue, verbose: Boolean = false)  = {
    // Get the initial views
    val (sav, initViews) = system.initViews; sysAbsViews = sav
    var newViews: Array[View] = initViews

    while(!done.get && ply <= bound){
      println("\nSTEP "+ply) 
      println("#abstractions = "+printLong(sysAbsViews.size))
      println("#new active abstract views = "+printInt(newViews.size))
      nextNewViews = new ArrayBuffer[View]
      for(v <- newViews) process(v)
      ply += 1; newViews = nextNewViews.toArray; 
      if(newViews.isEmpty) done.set(true)
    }
    println("\nSTEP "+ply)
    println("#abstractions = "+printLong(sysAbsViews.size))
    println(sysAbsViews)
  }


}









// ==================================================================
// ==================================================================
// Dead code below here


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



