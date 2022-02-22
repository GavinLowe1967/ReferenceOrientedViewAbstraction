package ViewAbstraction

import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.Remapper
import ViewAbstraction.CombinerP.Combiner
import ViewAbstraction.ExtendabilityP.Extendability
import scala.collection.mutable.{ArrayBuffer,HashSet,HashMap}
import java.util.concurrent.atomic.{AtomicLong,AtomicInteger,AtomicBoolean}

/** A checker for the view abstraction algorithm, applied to system.
  * @param aShapes the shapes of abstractions.
  * @param cShapes the shapes of concretizations. */
class Checker(system: SystemP.System){

  /** Exception thrown to indicate that an error transition has been found.
    * This is caught within process. */
  class FoundErrorException extends Exception

  /** The abstract views. */
  protected var sysAbsViews: ViewSet = null
  // Note: in various places, we iterate over sysAbsViews.  We should avoid
  // adding new views to the set while that is going on.

  def numViews = sysAbsViews.size

  /** The new views to be considered on the next ply. */
  protected var nextNewViews: MyHashSet[ComponentView] = null

  /** Utility object encapsulating the isExtendable function. */
  private var extendability: Extendability = _

  /** Utility object encapsulating the effectOn and completeDelayed
  * functions. */
  private var effectOn: EffectOn = _

  private def showTransition(
    pre: Concretization, e: EventInt, post: Concretization) =
    s"$pre -${system.showEvent(e)}-> $post"

  val Million = 1000000

  private var done = new AtomicBoolean(false); protected var ply = 1

  import TransitionSet.Transition // (Concretization, EventInt, Concretization)

  /* A Transition is a tuple (pre, e, post): (Concretization, EventInt,
   * Concretization), representing the transition pre -e-> post.  The pre
   * state extends a View by adding all relevant components: components that
   * synchronise on the transition, and any components to which the principal
   * component obtains a reference.*/

  /** The extended transitions found on previous plies.  Abstractly, a set of
    * Transitions.  */
  private val transitions: TransitionSet = new ServerBasedTransitionSet(16)

  /** Transitions found on this ply.  Transitions are initially added to
    * newTransitions, but transferred to transitions at the end of the ply. */
  private var newTransitions: BasicHashSet[Transition] = null

  import TransitionTemplateSet.TransitionTemplate
  // = (Concretization, Concretization, ProcessIdentity, EventInt, Boolean)

  /* A TransitionTemplate (pre, post, id, e, include): (Concretization,
   * Concretization, ProcessIdentity, EventInt, Boolean) represents an
   * extended transition pre U st -e-> post U st' for every state st and st'
   * such that (1) st and st' have identity id; (2) st is compatible with pre;
   * (3) if include then st -e-> st', otherwise st = st'.  */

  /** The transition templates found on previous plies.  Abstractly, a set of
    * TransitionTemplates. */
  private val transitionTemplates: TransitionTemplateSet = 
    new ServerBasedTransitionTemplateSet

  /** Transition templates found on this ply.  Transition templates are
    * initially added to newTransitionTemplates, but transferred to
    * transitionsTemplates at the end of the ply. */
  private var newTransitionTemplates: MyHashSet[TransitionTemplate] = null

  var addTransitionCount = 0L
  // var effectOfPreviousTransitionsCount = 0
  // var effectOnOthersCount = 0
  // var newViewCount = 0L
  // var addedViewCount = 0L
  // var effectOnRepetition = 0
  // var instantiateTransitionTemplateCount = 0L
  // Counts on transition templates

  /** Store the ExtendedTransition pre -> post, and calculate its effect on
    * previously found views. */
  @inline private 
  def addTransition(pre: Concretization, e: EventInt, post: Concretization)
  = {
    addTransitionCount += 1
    // assert(pre.ply < Int.MaxValue)
    // assert(post.ply < Int.MaxValue)
    val newTrans = ((pre, e, post))
    if(!transitions.contains(newTrans)){
      if(newTransitions.add(newTrans)) effectOnOthers(pre, e, post)
      // Note: the views of post get added to sysAbsViews within apply.
    }
  }

  // ========= Processing a single view

  /** Process v, calculating all the concrete transitions from v, adding the
    * post-states to sysAbsViews, and adding new ones to nextNewViews.
    * @return true if a concrete transition on error is generated. 
    */
  private def process(v: View): Boolean = { 
    if(verbose) println(s"\n**** Processing $v")
    // assert(v.ply < Int.MaxValue)
    v match{
      case cv: ComponentView =>
        if(debugging) StateArray.checkDistinct(cv.components)
        for((pre, e, post, outsidePid) <- system.transitions(cv)){
          // assert(pre.ply < Int.MaxValue)
          // assert(post.ply == Int.MaxValue); post.ply = ply
          if(showTransitions)
            println(s"$pre -${system.showEvent(e)}-> $post ["+
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
        // Effect of previous transitions on this view
        effectOfPreviousTransitions(cv)
        effectOfPreviousTransitionTemplates(cv)
        if(singleRef) effectOn.completeDelayed(cv, nextNewViews)
    }
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
      println(s"processTransition:\n  $pre -${system.showEvent(e)}-> $post"+
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
      s"$pre -${system.showEvent(e)}-> $post:\n"+
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
      // if(!newVersion) addViewFromConc(pre, e, post)
      // Store this transition, and calculate effect on other views.
      addTransition(pre, e, post)
    }
    else{ // Case 2: one new parameter from outside the view
      assert(newPids.length == 1) // simplifying assumption
      val newPid = newPids.head
      // Store transition template
      val newTransTemp = (pre, post, newPid, e, outsidePid != null)
      assert(!transitionTemplates.contains(newTransTemp)) // IMPROVE
      newTransitionTemplates.add(newTransTemp)
      // Try to find component of pre with non-omitted reference to newPid
      val preCpts = pre.components; val len = preCpts.length; 
      var i = 0; var done = false
      while(i < len && !done){
        // Test if preCpts(i) has non-omitted reference to newPid
        val cpt = preCpts(i); val pids = cpt.processIdentities; 
        // val includeInfo = State.getIncludeInfo(cpt.cs); 
        var j = 0
        while(j < pids.length && 
            (pids(j) != newPid || !cpt.includeParam(j))) // includeInfo != null && !includeInfo(j))) 
          j += 1
        if(j < pids.length) done = true
        else i += 1
      }
      if(i < len){
        instantiateTransitionTemplateViaRef(
          pre, post, newPid, e, outsidePid != null, preCpts(i))
      }
      else{
        // Counting of different types of TransitionTemplates; IMPROVE
        if(false){
          if(outsidePid != null) 
            Profiler.count("TransitionTemplate sync") // ~10%
          else{
            assert(pre.servers.servers.exists(
              _.processIdentities.contains(newPid)),
              s"pre = $pre; newPid = $newPid")
            Profiler.count("TransitionTemplate server") // ~30%
          }
        } // end of if(false)
        // Get extended transitions based on this
        instantiateTransitionTemplate(pre, post, newPid, e, outsidePid != null)
      }
    } // end of else
  }

  // ========= Extending TransitionTemplates 

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) based on prior views.
    * Called from processTransition. 
    * @throw FoundErrorException is a concrete transition on error is
    * generated. */
  private def instantiateTransitionTemplate(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean)  = {
    if(verbose) 
      println(s"instantiateTransitiontemplate($pre, $post, $newPid, "+
        s"${system.showEvent(e)}, $include)")
    Profiler.count("instantiateTransitionTemplate")
    val iter = sysAbsViews.iterator(pre.servers)
    while(iter.hasNext){
      val cv = iter.next
      instantiateTransitionTemplateBy(pre, post, newPid, e, include, cv)
    }
  }

  /** The effect of view cv on previous TransitionTemplates.
    *  Called from process. */
  private def effectOfPreviousTransitionTemplates(cv: ComponentView) = {
    val iter = transitionTemplates.iterator(cv.servers)
    while(iter.hasNext){
      val (pre, post, id, e, include) = iter.next
      // assert(pre.servers == cv.servers)
      instantiateTransitionTemplateBy(pre, post, id, e, include, cv)
    }
  }

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) and the view cv.  That is, find each renaming of cv
    * compatible with pre, and that includes a component with identity newPid
    * that optionally can perform oe.  For each, store the transition
    * (extending pre -> post with the transition of the component with
    * identity newPid), the post-state, and calculate the effect on other
    * views.  Called from instantiateTransitionTemplate and
    * effectOfPreviousTransitionTemplates. 
    * @throw FoundErrorException is a concrete transition on error is
    * generated.  */
  @inline private def instantiateTransitionTemplateBy(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean, cv: ComponentView)
  = {
    if(false && verbose) 
      println(s"instantiateTransitionTemplateBy:\n "+
        s"  $pre \n -${system.showEvent(e)}-> $post\n  $cv $newPid")
    Profiler.count("instantiateTransitionTemplateBy")
    require(pre.servers == cv.servers)
    // All states outsideSt that rename a state of cv to give a state with
    // identity newPid, and such that the renaming of cv is consistent with
    // pre; also the next-states of outsideSt after e (if e >= 0).
    val extenders = 
      system.consistentStates(pre, newPid, if(include) e else -1, cv)
    if(false) println(s"extenders = $extenders")
    var i = 0
    while(i < extenders.length){
      val (outsideSt, outsidePosts) = extenders(i); i += 1
      assert(outsidePosts.nonEmpty && 
        outsideSt.componentProcessIdentity == newPid) 
      extendTransitionTemplateBy(pre, post, e, outsideSt, outsidePosts, cv)
    }
  }

  /** Extend the transition template pre -e-> post by adding outsideSt.
    * @param outsidePosts the next state of outsideSt after e
    * @param cv the ComponentView giving the origin of outsideSt.
    * @throw FoundErrorException is a concrete transition on error is
    * generated.*/
  @inline private def extendTransitionTemplateBy(
    pre: Concretization, post: Concretization, e: EventInt, 
    outsideSt: State, outsidePosts: Array[State], cv: ComponentView) 
  = {
    if(false && verbose) 
      println(s"extendTransitionTemplateBy($pre, $post, ${system.showEvent(e)},"+
        s" $outsideSt)")
    // Profiler.count("instantiateTT1")
    val referencingViews = extendability.isExtendable(pre, outsideSt)
    if(false) println(s"referencingViews = $referencingViews")
    if(referencingViews != null){
      // Profiler.count("instantiateTT2")
      val extendedPre = pre.extend(outsideSt)
      // Set debugging info
      extendedPre.setSecondaryView(cv, referencingViews) 
      // var op = outsidePosts.toList // IMPROVE;
      var i = 0 
      while(i < outsidePosts.size){
        //while(op.nonEmpty){
        // Profiler.count("instantiateTT3")
        // val postSt = op.head; op = op.tail
        val postSt = outsidePosts(i); i += 1
        val extendedPost = post.extend(postSt)
        if(e == system.Error) throw new FoundErrorException
        // Store this transition, and calculate effect on other views.
        addTransition(extendedPre, e, extendedPost)
      }
    }
  }

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) based on prior views with a renamed version of
    * refState as the principal state.  Called from processTransition.
    * Pre: refState is a component of newPid, with a reference to newPid. */
  private def instantiateTransitionTemplateViaRef(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean, refState: State)
  = { 
    if(verbose) 
      println(s"** instantiateTransitionTemplateViaRef:\n "+
        s"$pre \n  -${system.showEvent(e)}-> $post from $refState")
    Profiler.count("instantiateTransitionTemplateViaRef") // ~60% of TTs
    // Look for views with following as principal
    val princ = Remapper.remapToPrincipal(pre.servers, refState)
    val iter = sysAbsViews.iterator(pre.servers, princ)
    while(iter.hasNext){
      val cv = iter.next
      instantiateTransitionTemplateBy(pre, post, newPid, e, include, cv)
      // IMPROVE: can simplify isExtendable, consistentStates, using the fact
      // that newPid is in position ix.
    }
  }

  // ========= Effect of transitions on other views

  /** Effect on other views of a transition pre -> post.  For every view v1 in
    * sysAbsViews, if it is consistent with pre (i.e. unifiable), and contains
    * at least one process that changes state, then update as per this
    * transition. */
  private 
  def effectOnOthers(pre: Concretization, e: EventInt, post: Concretization) = 
  if(pre != post){
    if(false) println(s"effectOnOthers $pre -${system.showEvent(e)}-> $post")
    // effectOnOthersCount += 1
    val iter = sysAbsViews.iterator(pre.servers)
    while(iter.hasNext){
      val cv = iter.next
      effectOn(pre, e, post, cv, nextNewViews)
    }
  }

  /** The effect of previously found extended transitions on the view cv. */
  private def effectOfPreviousTransitions(cv: ComponentView) = {
    // effectOfPreviousTransitionsCount += 1
    val iter = transitions.iterator(cv.servers)
    while(iter.hasNext){
      val (pre, e, post) = iter.next
      // println(s"considering transition $pre -> $post")
      // effectOnViaTransCount += 1
      effectOn(pre, e, post, cv, nextNewViews)
    }
  }

  // ========= Main function

  /** Run the checker. 
    * @param bound the number of plys to explore (with negative values meaning 
    * effectively infinite).  */
  def apply(bound: Int = Int.MaxValue)  = {
    // Get the initial views
    val (sav, initViews) = system.initViews; sysAbsViews = sav
    println("initViews = "+initViews.mkString("; "))
    // for(v <- initViews) assert(v.ply == 0)
    var newViews: Array[View] = initViews
    extendability = new Extendability(sysAbsViews)
    effectOn = new EffectOn(sysAbsViews, system)

    while(!done.get && ply <= bound){
      println("\nSTEP "+ply) 
      println("#abstractions = "+printLong(sysAbsViews.size))
      println(s"#transitions = ${printLong(transitions.size)}")
      println(s"#transition templates = ${printLong(transitionTemplates.size)}")
      println("#new active abstract views = "+printInt(newViews.size))
      nextNewViews = new BasicHashSet[ComponentView]
      newTransitions = new BasicHashSet[Transition]
      newTransitionTemplates = new BasicHashSet[TransitionTemplate]
      var i = 0

      // Process all views from newViews.
      while(i < newViews.length && !done.get){
        if(process(newViews(i))){
          done.set(true)
          val debugger = new Debugger(system, sysAbsViews, initViews)
          debugger(newViews(i))
          ??? // This should be unreachable.
        }
        i += 1
        if(i%50 == 0){ print("."); if(i%500 == 0) print(i) }
      }

      // Add views and transitions found on this ply into the main set.
      println(s"\nCopying: nextNewViews, ${nextNewViews.size}; "+
        s"newTransitions, ${newTransitions.size}; "+
        s"newTransitionTemplates, ${newTransitionTemplates.size}")
      val newViewsAB = new ArrayBuffer[ComponentView]
      def addView(v: ComponentView): Boolean = {
// FIXME: probably not if there's a missing ref. 
        if(sysAbsViews.add(v)){ 
          if(false) println(v)
          assert(v.representableInScript)
          // v.ply = ply
          newViewsAB += v; true 
        } 
        else false
      } // end of addView
      for((pre,e,post) <- newTransitions.iterator){
        assert(transitions.add(pre, e, post))
        // val v = Remapper.remapComponentView(post.toComponentView)
        for(v0 <- post.toComponentView){
          val v = Remapper.remapComponentView(v0)
          if(addView(v)){
            v.setCreationInfo(pre, e, post)
            if(showTransitions) 
              println(s"$pre -${system.showEvent(e)}->\n  $post gives $v")
          }
        }
      }
      if(verbose) // print newTransitions
        println(
          (for((pre,e,post) <- newTransitions.iterator.toArray)
          yield s"$pre -${system.showEvent(e)}->\n  $post"
          ).sorted.mkString("\n") )
      // Store new views, transition templates
      for((pre, post, id, e, inc) <- newTransitionTemplates.iterator)
        transitionTemplates.add(pre, post, id, e, inc)
      for(v <- nextNewViews.iterator){
        addView(v)
        // if(showTransitions){
        //   println(s"adding $v from nextNewViews")
        //   if(findTarget(v)){
        //     println("***")
        //     val (pre, cpts, cv, post, newComponents) = v.getCreationIngredients
        //     println(s"Adding  $cv -> $v\n"+
        //       s"$pre --> $post\n"+
        //       s"  induces $cv == ${View.show(pre.servers, cpts)}\n"+
        //       s"  --> ${View.show(post.servers, newComponents)} == $v")
        //   }
        // }
      }
      ply += 1; newViews = newViewsAB.toArray; 
      if(showEachPly)
        println("newViews =\n"+newViews.map(_.toString).sorted.mkString("\n"))
      if(newViews.isEmpty) done.set(true)
      // if(false && ply > 15) println(sysAbsViews.summarise1)
    } // end of main loop

    println("\nSTEP "+ply+"\n")
    if(singleRef && bound == Int.MaxValue) effectOn.sanityCheck
    // Following is expensive: IMPROVE: enable via switch
    if(singleRef) effectOn.report
    if(showViews) println(sysAbsViews)
    if(false) println(sysAbsViews.summarise)
    println("#abstractions = "+printLong(sysAbsViews.size))
    println(s"#transitions = ${printLong(transitions.size)}")
    println(s"#transition templates = ${printLong(transitionTemplates.size)}")
    
    // println(s"effectOnStore size = "+effectOnStore.size)
  }

  //import java.lang.reflect.Modifier
  // import ox.gavin.profiling._
  import ox.gavin.profiling.MemoryProfiler.traverse  

  // def printObjectSize(obj: Object) = {
  //   println("Object type: " + obj.getClass() +
  //             ", size: " + InstrumentationAgent.getObjectSize(obj) + " bytes")
  // }

  /** Perform a memory profile of this. */
  def memoryProfile = {
    println("Memory profile"); println

    println("# states = "+MyStateMap.stateCount)
    traverse("MyStateMap", MyStateMap, maxPrint = 0); println

    traverse("ServerStates", ServerStates, maxPrint = 0); println

    traverse("first view", sysAbsViews.iterator.next, maxPrint = 0); println

    traverse("sysAbsViews", sysAbsViews, maxPrint = 0); println

    traverse("transitions", transitions, maxPrint = 0); println

    traverse("transitionTemplates", transitionTemplates, maxPrint = 0); println

    traverse("extendability", extendability, maxPrint = 0); println

    if(true){
      //traverse("system.components", system.components, maxPrint = 2); println
      traverse("system", system, maxPrint = 1); println }
    else println("Omitting system\n") 

    traverse("effectOn", effectOn, maxPrint = 5, maxPrintArray = 8); println

    traverse("checker", this, maxPrint = 0); println
  }
}






