package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
import collection.{MyHashSet,BasicHashSet,ShardedHashSet}
import scala.collection.mutable.{ArrayBuffer}

/** The state of a check. 
  * @param system the system being explored.
  * @param initViewSet the initial set of views. */
class CheckerState(system: SystemP.System, initViewSet: ViewSet){

  /** The abstract views. */
  var sysAbsViews: ViewSet = initViewSet

  def numViews = sysAbsViews.size

  protected type NextNewViewSet = ShardedHashSet[ComponentView]

  /** The new views to be considered on the next ply. */
  var nextNewViews: NextNewViewSet = null

  /** Initialise nextNewViews.  Used by CheckerTest. */
  def initNextNewViews = nextNewViews = new NextNewViewSet

  /* The transitions found so far. */
  private val transitions = new NewTransitionSet

  private type NextTransitionSet = ShardedHashSet[Transition]

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

  /* Initialise utility object encapsulating the effectOn and completeDelayed
   * functions. */
  EffectOn.init(sysAbsViews, system)

  /** Utility object for extending transition templates. */
  private val transitionTemplateExtender = 
    new TransitionTemplateExtender(transitionTemplates, system, sysAbsViews)

  // var addTransitionCount = 0L

  /** Add trans to the set of transitions, and induce new transitions on
    * existing views. */
  private def addTransition(trans: Transition): Unit = {
    // addTransitionCount += 1
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
  // private def process(cv: ComponentView): Boolean = { 
  //   if(processViewTransitions(cv)) return true
  //   // Effect of previous transitions on this view
  //   effectOfPreviousTransitions(cv)
  //   // Effect of previous transition templates
  //   addTransitions(
  //     transitionTemplateExtender.effectOfPreviousTransitionTemplates(cv) )
  //   if(singleRef) EffectOn.completeDelayed(cv, nextNewViews)
  //   false
  // } 

  /** Process the view transitions from cv.  
    * @return true if a concrete transition on error is generated. 
    */
  @inline def processViewTransitions(cv: ComponentView): Boolean = {
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
  def effectOfPreviousTransitions(cv: ComponentView) = {
    val iter = transitions.iterator(cv)
    while(iter.hasNext){ 
      val t = iter.next()
      // Note: second clause is because another transition in the same batch
      // might have succeeded.
/*    assert(t.mightGiveSufficientUnifs(cv) || 
          cv.containsDoneInduced(t.post.servers),
        s"t = $t;\n cv = $cv\n"+cv.containsDoneInduced(t.post.servers)) */
      new EffectOn(t, cv, nextNewViews)()
    }
  }

  // Extending transition templates

  /** Try instantiating previous transition templates with view. */
  @inline def instantiateTransitiontemplates(view: ComponentView) =
    addTransitions(
      transitionTemplateExtender.effectOfPreviousTransitionTemplates(view) )

  //----------------------  Administrative functions, start and end of ply

  /** Buffer that accumulated views found on one ply for the next ply. */
  private var viewsBuff: ConcurrentBuffer[ComponentView] = null

  /** Producer for iterators for copying views found on one ply, ready for the
    * next ply.  Set by worker 0 on each ply. */
  private var viewShardIteratorProducer: 
      ShardedHashSet.ShardIteratorProducerT[ComponentView] = null

  /** Producer for iterators for copying transitions found on one ply, ready for
    * the next ply.  Set by worker 0 on each ply. */
  private var transitionShardIteratorProducer: 
      ShardedHashSet.ShardIteratorProducerT[Transition] = null

  /** Get the views for the next ply. */
  def getNewViews: Array[ComponentView] = viewsBuff.get

  /** Prepare for the next ply.  Performed by thread 0. */
  def startOfPly = {
    println("#abstractions = "+printLong(sysAbsViews.size))
    println(s"#transitions = ${printLong(transitions.size)}")
    println(s"#transition templates = ${printLong(transitionTemplates.size)}")
    // println("#new active abstract views = "+printInt(newViews.size))
    nextNewViews = new NextNewViewSet
    newTransitions = new NextTransitionSet
    newTransitionTemplates = new BasicHashSet[TransitionTemplate]

    // Initialise objects ready for end of ply
    viewsBuff = new ConcurrentBuffer[ComponentView](numWorkers)
    viewShardIteratorProducer = nextNewViews.shardIteratorProducer
    transitionShardIteratorProducer = newTransitions.shardIteratorProducer
// FIXME
    if(singleRef && !useNewEffectOnStore) EffectOn.prepareForPurge
  }

  /** Add v to sysAbsViews and viewsBuff if new.  Return true if so. */
  def addView(me: Int, v: ComponentView): Boolean = {
    if(ComponentView0.highlight(v)) println(s"adding $v")
    if(sysAbsViews.add(v)){
      assert(v.representableInScript); viewsBuff.add(me, v); true
    }
    else false
  } // end of addView

  /** Updates at the end of a ply. */
  def endOfPly(me: Int) = {
    if(me == 0){
      // Worker 0 prints info and copies transition templates.
      print(s"\nCopying: nextNewViews, ${nextNewViews.size}; ")
      print(s"newTransitionTemplates, ${newTransitionTemplates.size}; ")
      println(s"newTransitions, ${newTransitions.size}. ")
      for(template <- newTransitionTemplates.iterator)
        transitionTemplates.add(template)
    }
    // Thread 1 maybe does a garbage collection
    else if(me == 1 && doGC && ply%4 == 0 && EffectOn.doPurge){
      print("Garbage collection..."); java.lang.System.gc(); println(".  Done.")
    }

    // Purges from the effectOnStore
    if(singleRef && !useNewEffectOnStore) EffectOn.purge
// FIXME

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
            if(ComponentView0.highlight(v)) println(s"adding $v from $t")
            v.setCreationTrans(t) 
            if(showTransitions) println(s"${t.toString}\ngives $v")
          }
        }
      } // end of iteration over transIter
      transIter = transitionShardIteratorProducer.get
    }
  }

  /** Reporting at the end of a check. */
  def endOfCheck = {
    if(showViews) println(sysAbsViews)
    println("#abstractions = "+printLong(sysAbsViews.size))
    println(s"#transitions = ${printLong(transitions.size)}")
    println(s"#transition templates = ${printLong(transitionTemplates.size)}")
  }

  /** Memory profiling. */
  def memoryProfile = {
    import ox.gavin.profiling.MemoryProfiler.traverse
    // Traverse 3 views.  Not very useful as mostly in creationIngredients.
    val viewsIter = sysAbsViews.iterator
    for(_ <- 0 until 3; if viewsIter.hasNext){
      traverse("ComponentView", viewsIter.next(), maxPrint = 1); println()
    }
    traverse("sysAbsViews", sysAbsViews, maxPrint = 1); println()
    traverse("transitions", transitions, maxPrint = 0); println()
    traverse("transitionTemplates", transitionTemplates, maxPrint = 0); println()
    // traverse("extendability", extendability, maxPrint = 0); println()
    traverse("transitionTemplateExtender", transitionTemplateExtender, 
      maxPrint = 1, ignore = List("System"))
    println()
    traverse("CheckerState", this, maxPrint = 0, ignore = List("System"))
  }

}
