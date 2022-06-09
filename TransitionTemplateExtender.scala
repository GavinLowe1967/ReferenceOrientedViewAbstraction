package ViewAbstraction

import ViewAbstraction.ExtendabilityP.Extendability
import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.ArrayBuffer
import ox.gavin.profiling.Profiler

/** Utility object to extend transition templates. */ 
class TransitionTemplateExtender(
  transitionTemplates: TransitionTemplateSet, 
  system: SystemP.System, sysAbsViews: ViewSet
){

  /** Utility object encapsulating the isExtendable function. */
  private var extendability: Extendability = new Extendability(sysAbsViews)

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
    * instantiateTransitionTemplate and effectOfPreviousTransitionTemplates.
    * @throw FoundErrorException is a concrete transition on error is
    * generated.  */
  @inline private def instantiateTransitionTemplateBy(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean, cv: ComponentView, 
    buffer: Buffer)
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
      extendTransitionTemplateBy(
        pre, post, e, outsideSt, outsidePosts, cv, buffer)
    }
  }

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) based on prior views with a renamed version of
    * refState as the principal state.  Called from Checker.processTransition.
    * Pre: refState is a component of newPid, with a reference to newPid. */
  def instantiateTransitionTemplateViaRef(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean, refState: State)
      : Buffer = {
    if(verbose) 
      println(s"** instantiateTransitionTemplateViaRef:\n "+
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

  /** Produce ExtendedTransitions from the TransitionTemplate (pre, post,
    * newPid, e, include) based on prior views.
    * Called from Checker.processTransition. 
    * @throw FoundErrorException is a concrete transition on error is
    * generated. */
  def instantiateTransitionTemplate(
    pre: Concretization, post: Concretization, 
    newPid: ProcessIdentity, e: EventInt, include: Boolean)
      : Buffer  = {
    if(verbose) 
      println(s"instantiateTransitiontemplate($pre, $post, $newPid, "+
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

}

// ==================================================================
    
/** Exception thrown to indicate that an error transition has been found.
  * This is caught within process. */
class FoundErrorException extends Exception
