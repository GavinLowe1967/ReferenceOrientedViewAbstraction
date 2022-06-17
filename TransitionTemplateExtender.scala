package ViewAbstraction

import ViewAbstraction.ExtendabilityP.Extendability
import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.ArrayBuffer
import ox.gavin.profiling.Profiler

/* Relationship of classes.
 * TransitionTemplateExtender
 * |- ConsistentStateFinder
 * |  |- Combiner
 * |- Extendability
 *    |- Combiner
 * The latter classes aren't accessed elsewhere. 
 */

/** Utility object to extend transition templates. */ 
class TransitionTemplateExtender(
  transitionTemplates: TransitionTemplateSet, 
  system: SystemP.System, sysAbsViews: ViewSet
){
  /* Extend a particular transition template by a particular view.  Private.  
   * Called from various places below.
   * instantiateTransitionTemplateBy
   * |- ConsistentStateFinder.consistentStates
   * |- extendTransitionTemplateBy
   *    |- Extendability.isExtendable

   * Instantiate a particular transition template via all previous views.
   * Called from Checker.processTransition
   * instantiateTransitionTemplate
   * |- instantiateTransitionTemplateViaRef
   * |  |- sysAbsViews.iterator
   * |  |- instantiateTransitionTemplateBy
   * |- instantiateTransitionTemplateAll
   *    |- sysAbsViews.iterator
   *    |- instantiateTransitionTemplateBy
   * 
   * Instantiate all previous transition templates via a particular view.  
   * Called from Checker.process.
   * effectOfPreviousTransitionTemplates
   * |- transitionTemplates.iterator
   * |- instantiateTransitionTemplateBy
   */


  /** Utility object encapsulating the isExtendable function. */
  private var extendability: Extendability = new Extendability(sysAbsViews)

  private val consistentStateFinder = new ConsistentStateFinder(system)

  type Buffer = ArrayBuffer[Transition]

  /** Extend the transition template pre -e-> post by adding outsideSt.  Add
    * each to buffer.
    * @param outsidePosts the next state of outsideSt after e
    * @param cv the ComponentView giving the origin of outsideSt.
    * @throw FoundErrorException is a concrete transition on error is
    * generated.*/
  @inline private def extendTransitionTemplateBy(
    pre: Concretization, post: Concretization, e: EventInt, 
    outsideSt: State, outsidePosts: Array[State], cv: ComponentView, 
    buffer: Buffer)
  = {
    if(false && verbose) 
      println(s"extendTransitionTemplateBy($pre, $post, ${system.showEvent(e)},"+
        s" $outsideSt)")
    val referencingViews = extendability.isExtendable(pre, outsideSt)
    if(false) println(s"referencingViews = $referencingViews")
    if(referencingViews != null){
      val extendedPre = pre.extend(outsideSt)
      // Set debugging info
      extendedPre.setSecondaryView(cv, referencingViews) 
      var i = 0 
      while(i < outsidePosts.size){
        val postSt = outsidePosts(i); i += 1
        val extendedPost = post.extend(postSt)
        if(e == system.Error) throw new FoundErrorException
        // Store this transition, and calculate effect on other views.
        buffer += new Transition(extendedPre, e, extendedPost)
        // addTransition(extendedPre, e, extendedPost)
      }
    }
  }

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) and the view cv.  That is, find each renaming of cv
    * compatible with pre, and that includes a component with identity newPid
    * that optionally can perform oe.  Add each to buffer.  Called from
    * instantiateTransitionTemplateViaRef, instantiateTransitionTemplateAll,
    * and effectOfPreviousTransitionTemplates.  If onlyPrinc, consider only
    * renamings of cv.princ.
    * @throw FoundErrorException is a concrete transition on error is
    * generated.  */
  @inline private def instantiateTransitionTemplateBy(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean, cv: ComponentView, 
    buffer: Buffer)
  = {
    // val highlight = 
    //   { val servers = post.servers.servers; 
    //     servers(0).cs == 32 && servers(1).cs == 33 }  &&
    //      post.components(0).cs == 26  && post.components(1).cs == 10
    if(false) println(s"instantiateTransitionTemplateBy:\n "+
        s"  $pre \n -${system.showEvent(e)}-> $post\n  $cv $newPid")
    Profiler.count("instantiateTransitionTemplateBy")
    require(pre.servers == cv.servers)
    // All states outsideSt that rename a state of cv to give a state with
    // identity newPid, and such that the renaming of cv is consistent with
    // pre; also the next-states of outsideSt after e (if e >= 0).
    val extenders = consistentStateFinder.consistentStates(
      pre, newPid, if(include) e else -1, cv)
    var i = 0
    while(i < extenders.length){
      val (outsideSt, outsidePosts) = extenders(i); i += 1
      assert(outsidePosts.nonEmpty && 
        outsideSt.componentProcessIdentity == newPid) 
      extendTransitionTemplateBy(
        pre, post, e, outsideSt, outsidePosts, cv, buffer)
    }
  }


  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) based on prior views with a renamed version of
    * refState as the principal state. 
    * Pre: refState is a component of newPid, with a reference to newPid. */
  private def instantiateTransitionTemplateViaRef(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean, refState: State)
      : Buffer = {
    if(verbose) println(s"instantiateTransitionTemplateViaRef:\n "+
        s"$pre \n  -${system.showEvent(e)}-> $post from $refState")
    val buffer = new Buffer
    Profiler.count("instantiateTransitionTemplateViaRef") // ~60% of TTs
    // Look for views with following as principal
    val princ = Remapper.remapToPrincipal(pre.servers, refState)
    val iter = sysAbsViews.iterator(pre.servers, princ)
    while(iter.hasNext){
      val cv = iter.next()
      instantiateTransitionTemplateBy(pre, post, newPid, e, include, cv, buffer)
      // IMPROVE: can simplify isExtendable, consistentStates, using the fact
      // that newPid is in position ix.
    }
    buffer
  }


  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) based on prior views.
    * @throw FoundErrorException is a concrete transition on error is
    * generated. */
  private def instantiateTransitionTemplateAll(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean)
      : Buffer  = {
    if(verbose) println(s"instantiateTransitiontemplate($pre, $post, $newPid, "+
        s"${system.showEvent(e)}, $include)")
    val buffer = new Buffer
    Profiler.count("instantiateTransitionTemplate")
    val iter = sysAbsViews.iterator(pre.servers)
    while(iter.hasNext){
      val cv = iter.next()
      instantiateTransitionTemplateBy(pre, post, newPid, e, include, cv, buffer)
    }
    buffer
  }

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) based on prior views. 
    * Called from Checker.processTransition.
    * @throw FoundErrorException is a concrete transition on error is
    * generated. */
  def instantiateTransitionTemplate(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean) 
      : Buffer = {
    // Try to find component of pre with non-omitted reference to newPid
    val preCpts = pre.components; val len = preCpts.length;
    var i = 0; var done = false
    while(i < len && !done){
      // Test if preCpts(i) has non-omitted reference to newPid
      val cpt = preCpts(i); val pids = cpt.processIdentities; var j = 0
      while(j < pids.length && (pids(j) != newPid || !cpt.includeParam(j)))
        j += 1
      if(j < pids.length) done = true else i += 1
    }
    // Instantiate transition template to create extended transitions,
    // possibly making use of the reference from preCpts(i).
    if(i < len)
      instantiateTransitionTemplateViaRef(
        pre, post, newPid, e, include, preCpts(i))
    else instantiateTransitionTemplateAll(pre, post, newPid, e, include)
  }

  /** The effect of view cv on previous TransitionTemplates.
    *  Called from Checker.process. */
  def effectOfPreviousTransitionTemplates(cv: ComponentView): Buffer = {
    val buffer = new Buffer
    val iter = transitionTemplates.iterator(cv.servers)
    while(iter.hasNext){
      val (pre, post, id, e, include) = iter.next()
      // assert(pre.servers == cv.servers)
      instantiateTransitionTemplateBy(pre, post, id, e, include, cv, buffer)
    }
    buffer
  }

}

// ==================================================================
    
/** Exception thrown to indicate that an error transition has been found.
  * This is caught within process. */
class FoundErrorException extends Exception
