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

  // Note: there does seem to be some duplication of work between
  // ConsistentStateFinder.consistentStates and Extendability.isExtendable.
  // The former takes the additional state as an arbitrary state of a view.
  // The latter considers views with the additional state as principal.

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
    template: TransitionTemplate, outsideSt: State, outsidePosts: Array[State],
    cv: ComponentView, buffer: Buffer)
  = {
// [107(N0) || 109(N0) || 110() || 113() || 119() || 1()] ||
//   [36(T0,N1,N2,N0) || 10(N1,N3,N2) || 10(N3,Null,N1)]
// -get.T0.N1.N3.false.GetNoSignal->
// [107(N0) || 109(N0) || 110() || 113() || 119() || 1()] || 
//   [31(T0,N3,N1,N2) || 10(N1,N3,N2) || 10(N3,Null,N1)]
    val highlight =  false
      // ComponentView0.highlightPrev(template.pre) && 
      // ComponentView0.highlightNext(outsideSt)
    if(highlight) println(s"extendTransitionTemplateBy($template, $outsideSt)")
    val referencingViews = 
      if(singleRef && useNewReferencingViews) 
        checkCrossRefViews(template.pre, outsideSt)
      else extendability.isExtendable(template.pre, outsideSt)
    if(highlight) 
      println("referencingViews = "+
        (if(referencingViews==null) "null" else referencingViews.mkString("; ")))
    if(referencingViews != null){
      val extendedPre = template.pre.extend(outsideSt)
      // Set debugging info
      extendedPre.setSecondaryView(cv, referencingViews) 
      template.addDoneExtend(outsideSt)
      var i = 0 
      while(i < outsidePosts.size){
        val postSt = outsidePosts(i); i += 1
        val extendedPost = template.post.extend(postSt)
        if(template.e == system.Error) throw new FoundErrorException
        // Store this transition, and calculate effect on other views.
        buffer += new Transition(extendedPre, template.e, extendedPost)
      }
    }
  }

  /** Check that for every reference from a component of pre to outsideSt, or
    * vice versa, there is a corresponding view in sysAbsViews.  If so, return
    * those views.  If there are no such cross references, then return an
    * arbitrary view with outsideSt as principal.  If the required view(s) are
    * not in sysAbsViews then return null. */
  private def checkCrossRefViews(pre: Concretization, outsideSt: State)
      : Array[ComponentView] = {
    require(singleRef)
    val refViews = new ArrayBuffer[ComponentView]
    val cpts = pre.components; val servers = pre.servers
    // val highlight = 
    //   ComponentView0.highlightServers(servers) && cpts(0).cs == 33 &&
    //     outsideSt.cs == 32 && outsideSt.ids.sameElements(Array(0,0,1,-1))
    // if(highlight) println(s"checkCrossRefViews($pre, $outsideSt)")
    var i = 0; var ok = true
    /* If st1 has an included reference to st2, check sysAbsViews contains a
     * corresponding state, and add to refViews; otherwise set ok to false. */
    @inline def checkStates(st1: State, st2: State) = {
      if(st1.hasIncludedParam(st2.componentProcessIdentity)){
        val v1 = Remapper.mkComponentView(servers, Array(st1, st2))
        if(sysAbsViews.contains(v1)) refViews += v1
        else{ ok = false /*; if(highlight) println(s"Not found $v1")*/ }
      }
    }
    // Consider each component of pre in turn
    while(i < cpts.length && ok){
      val cpt = cpts(i); i += 1; 
      checkStates(cpt, outsideSt); if(ok) checkStates(outsideSt, cpt)
    } // end of while loop

    if(ok){
      if(refViews.nonEmpty) refViews.toArray
      else{
        // Test if sysAbsViews contains at least one view with renamed
        // outsideSt as principal.
        val renamedOutsideSt = Remapper.remapToPrincipal(servers, outsideSt)
        val iter = sysAbsViews.iterator(servers, renamedOutsideSt)
        if(iter.nonEmpty) Array(iter.next()) else null
      }
      // Do we need to include iter.next() in the "if" case, to help with
      // debugging?
    }
    else null
  }


  /** Produce ExtendedTransitions from template and the view cv.  That is, find
    * each renaming of cv compatible with template.pre, and that includes a
    * component with identity template.newPid that can perform template.e if
    * non-negative.  Add each to buffer.  Called from
    * instantiateTransitionTemplateViaRef, instantiateTransitionTemplateAll,
    * and effectOfPreviousTransitionTemplates.
    * @throw FoundErrorException is a concrete transition on error is
    * generated.  */
  @inline private def instantiateTransitionTemplateBy(
    template: TransitionTemplate, cv: ComponentView, buffer: Buffer)
  = {
    // val highlight =   ComponentView0.highlightPrev(template.pre) &&
    //     cv.components.exists(_.cs == 13)
    // if(highlight) println(s"instantiateTransitionTemplateBy($template, $cv)")
    require(template.pre.servers == cv.servers)
    // All states outsideSt that rename a state of cv to give a state with
    // identity newPid, and such that the renaming of cv is accordant with
    // pre; also the next-states of outsideSt after e (if e >= 0).
    val extenders = consistentStateFinder.consistentStates(
      template.pre, template.id, if(template.include) template.e else -1, cv)
    var i = 0
    while(i < extenders.length){
      val (outsideSt, outsidePosts) = extenders(i); i += 1
      // if(highlight && outsideSt.cs == 13) println(s"outsideSt = $outsideSt")
      assert(outsidePosts.nonEmpty &&
        outsideSt.componentProcessIdentity == template.id)
      if(!template.containsDoneExtend(outsideSt))
        extendTransitionTemplateBy(template, outsideSt, outsidePosts, cv, buffer)
    }
  }


  /** Produce ExtendedTransitions from template based on prior views with a
    * renamed version of refState as the principal state.  Pre: refState is a
    * component of newPid, with a reference to newPid. */
  private def instantiateTransitionTemplateViaRef(
    template: TransitionTemplate, refState: State)
      : Buffer = {
    val buffer = new Buffer
    Profiler.count("instantiateTransitionTemplateViaRef") // ~60% of TTs
    // Look for views with following as principal
    val princ = Remapper.remapToPrincipal(template.pre.servers, refState)
    val iter = sysAbsViews.iterator(template.pre.servers, princ)
    while(iter.hasNext){
      val cv = iter.next()
      instantiateTransitionTemplateBy(template, cv, buffer)
      // IMPROVE: can simplify isExtendable, consistentStates, using the fact
      // that newPid is in position ix.
    }
    buffer
  }


  /** Produce ExtendedTransitions from template based on prior views.
    * @throw FoundErrorException is a concrete transition on error is
    * generated. */
  private def instantiateTransitionTemplateAll(template: TransitionTemplate)
      : Buffer  = {
    val buffer = new Buffer
    Profiler.count("instantiateTransitionTemplate")
    val iter = sysAbsViews.iterator(template.pre.servers)
    while(iter.hasNext){
      val cv = iter.next()
      instantiateTransitionTemplateBy(template, cv, buffer)
    }
    buffer
  }

  /** Produce ExtendedTransitions from template based on prior views. 
    * Called from Checker.processTransition.
    * @throw FoundErrorException is a concrete transition on error is
    * generated. */
  def instantiateTransitionTemplate(template: TransitionTemplate) 
      : Buffer = {
    // if(ComponentView0.highlightPrev(template.pre))
    //   println(s"instantiateTransitionTemplate($template)")
    // Try to find component of pre with non-omitted reference to template.id
    val preCpts = template.pre.components; val len = preCpts.length;
    var i = 0; var done = false; val (f,id) = template.id
    while(i < len && !done){
      // Test if preCpts(i) has non-omitted reference to template.id
      val cpt = preCpts(i)
      if(cpt.hasIncludedParam(f,id)) done = true else i += 1
/*
      val pids = cpt.processIdentities; var j = 0
      while(j < pids.length && (pids(j) != template.id || !cpt.includeParam(j)))
        j += 1
      if(j < pids.length) done = true else i += 1
 */
    }
    // Instantiate transition template to create extended transitions,
    // possibly making use of the reference from preCpts(i).
    if(i < len)
      instantiateTransitionTemplateViaRef(template, preCpts(i))
    else instantiateTransitionTemplateAll(template)
  }

  /** The effect of view cv on previous TransitionTemplates.
    * Called from Checker.process. */
  def effectOfPreviousTransitionTemplates(cv: ComponentView): Buffer = {
    val buffer = new Buffer
    val iter = transitionTemplates.iterator(cv.servers)
    while(iter.hasNext){
      val template = iter.next()    // assert(iter.pre.servers == cv.servers)
      instantiateTransitionTemplateBy(template, cv, buffer)
    }
    buffer
  }

}

// ==================================================================
    
/** Exception thrown to indicate that an error transition has been found.
  * This is caught within process. */
class FoundErrorException extends Exception
