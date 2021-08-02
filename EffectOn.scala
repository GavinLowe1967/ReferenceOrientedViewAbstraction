package ViewAbstraction

import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.{Remapper,Unification}

import scala.collection.mutable.{ArrayBuffer}

/** A utility object, encapsulating the effectOn and completeDelayed
  * functions.  These describe the effect that one transition has on another
  * View. */
class EffectOn(views: ViewSet, system: SystemP.System){

  /** A mapping showing which component views might be added later.
    * Abstractly it stores tuples (missing, missingCommon, nv) such that:
    * missing is a set of views; missingCommon is a set of (ServerStates, State,
    * State, ProcessIdentity) tuples; and nv is a view.  If
    * 
    * (1) all the views in missing are added; and
    * 
    * (2) views are added so all elements of missingCommon satisfy
    * hasCommonRef; i.e. for each (servers, princ1, princ2, pid) in
    * missingCommon, there is a component state c with identity pid such that
    * servers || princ1 || c and servers || princ2 || c are both in sysAbsViews
    * (up to renaming);
    * 
    * then nv can also be added.
    * 
    * Tuples are added to the store in apply when a transition is prevented
    * because relevant views are not yet in the store.  completeDelayed
    * subsequently tries to complete the transitions.  */
  private val effectOnStore: EffectOnStore = new SimpleEffectOnStore

  /** The effect of the transition pre -e-> post on cv.  Create extra views
    * caused by the way the transition changes cv, and add them to
    * nextNewViews. */
  def apply(
    pre: Concretization, e: EventInt, post: Concretization, cv: ComponentView, 
    ply: Int, nextNewViews: MyHashSet[ComponentView])
  = {
    // Profiler.count("effectOn")
    if(verbose) println(s"effectOn($pre, ${system.showEvent(e)},\n  $post, $cv)")
    require(pre.servers == cv.servers && pre.sameComponentPids(post))
    val postCpts = post.components; val preCpts = pre.components
    // In the case of singleRef, secondary components that might gain a
    // reference to c2 = cv.principal (without unification): all pairs (i,id)
    // (i >= 1) such that the i'th  component c1 changes state, and id is a
    // parameter of c1 in the post state that might reference c2, distinct
    // from any component identity in pre, post.  We will subsequently form
    // views with c1 as the principal component, referencing c2 (renamed).
    val c2Refs = 
      if(singleRef) getCrossReferences(preCpts, postCpts, cv.principal.family)
      else List[(Int,Identity)]()
    // All remappings of cv to unify with pre, together with the list of
    // indices of unified components.
    val newCpts: ArrayBuffer[(Array[State], List[(Int,Int)])] =
      Unification.combine(pre, post, cv, c2Refs.map(_._2)) // IMPROVE 
    var cptIx = 0

    while(cptIx < newCpts.length){
      Profiler.count("EffectOn step")
      val (cpts, unifs) = newCpts(cptIx); cptIx += 1
      if(verbose) println("cpts = "+StateArray.show(cpts))
      if(debugging){
        StateArray.checkDistinct(cpts); assert(cpts.length==cv.components.length)
      }
      // If singleRef, identities of components referenced by both principals,
      // but not included in the views, and such that there is no way of
      // instantiating them consistently within sysAbsViews.
      // val commonMissing: List[ProcessIdentity] = 
      val missingCommons: List[MissingCommon] = 
        if(singleRef && !pre.components.sameElements(cv.components)) 
          checkCompatibleMissing(pre.servers, preCpts, cpts)
        else List()
      // If singleRef and there are references between components from pre and
      // cv, then check that that combination is possible in sysAbsViews:
      // those that are missing.
      val missing: List[ComponentView] =
        if(singleRef) missingCrossRefs(pre.servers, cpts, preCpts) else List() 
      // What does cpts(0) get mapped to?  IMPROVE: we don't need all of unifs
      var us = unifs; while(us.nonEmpty && us.head._1 != 0) us = us.tail
      val newPrinc = if(us.isEmpty) cpts(0) else postCpts(us.head._2)
      var newComponentsList =
        StateArray.makePostComponents(newPrinc, postCpts, cpts)
      // If singleRef and the secondary component of post has gained a
      // reference to newPrinc, we also build views corresponding to those two
      // components.
      for((i,id) <- c2Refs; if id == newPrinc.ids(0))
        newComponentsList ::= Array(postCpts(i), newPrinc)
      for(newComponents <- newComponentsList){
        val nv = Remapper.mkComponentView(post.servers, newComponents)
        Profiler.count("newViewCount")       // Mostly with unifs.nonEmpty
        if(!views.contains(nv)){
          // if(singleRef && !nextNewViews.contains(nv) && 
          //   (newComponents.length == 1 || newComponents(1) != newPrinc) && 
          //   pre.servers != post.servers && unifs.isEmpty)
          //   assert(Unification.eOCSCContains(cv, post.servers),
          //     s"\n$pre -${system.showEvent(e)}-> $post\n"+
          //       s"  with unifications $unifs\nc2Refs = $c2Refs\n"+
          //       s"  induces $cv == ${View.show(pre.servers, cpts)}\n"+
          //       s"  --> ${View.show(post.servers, newComponents)} == $nv")
          if(missing.isEmpty && missingCommons.isEmpty && nextNewViews.add(nv)){
            // if(singleRef) // IMPROVE
            //   assert(pre.servers != post.servers || unifs.nonEmpty || 
            //     newComponents(1) == newPrinc,
            //     s"\n$pre -${system.showEvent(e)}-> $post\n"+
            //       s"  with unifications $unifs\nc2Refs = $c2Refs\n"+
            //       s"  induces $cv == ${View.show(pre.servers, cpts)}\n"+
            //       s"  --> ${View.show(post.servers, newComponents)} == $nv")
            Profiler.count("addedViewCount")
            if(verbose /* || newComponents(0) != newPrinc */) println(
              s"$pre -${system.showEvent(e)}-> $post\n"+
                s"  with unifications $unifs\n"+
                s"  induces $cv == ${View.show(pre.servers, cpts)}\n"+
                s"  --> ${View.show(post.servers, newComponents)} == $nv")
            nv.setCreationInfoIndirect(
              pre, cpts, cv, e, post, newComponents, ply)
            if(!nv.representableInScript){
              println("Not enough identities in script to combine transition\n"+
                s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
              sys.exit
            }
          } // end of if(missing.isEmpty && nextNewViews.add(nv))
          else if(missing.nonEmpty || missingCommons.nonEmpty){
            // Note: we create nv eagerly, even if missing is non-empty: this
            // might not be the most efficient approach.  Note also that the
            // missingCommons may be shared.
            effectOnStore.add(missing, missingCommons, nv)
            if(verbose) println(s"Storing $missing, $missingCommons -> $nv")
            //if(verbose) println(s"Storing $missing, $commonMissingTuples -> $nv")
            nv.setCreationInfoIndirect(
              pre, cpts, cv, e, post, newComponents, ply)
          }
        } // end of if(!views.contains(nv))
      } // end of for loop
    } // end of while loop
  }
// IMPROVE: in the calculation of c2Refs, I think we can omit params of
// pre.servers other than cv.principal's identity.
// IMPROVE: could we have more simply achieved the effect of c2Refs by using
// cv with pre.principal as principal, and c2 as secondary component?  This
// assumes pre.principal has a reference to c2, which seems reasonable.


  /** Identify secondary components that can gain a reference to a component of
    * type f.  All pairs (i,id) (with i >= 1) such that the i'th component c1
    * changes state between preCpts and postCpts, and id is a
    * non-distinguished parameter of c1 of family f in the post state, other
    * than an identity in preCpts/postCpts. */
  @inline private 
  def getCrossReferences(
    preCpts: Array[State], postCpts: Array[State], f: Family)
      : List[(Int,Identity)] = {
    // Identities in pre: improve
    val ids = preCpts.filter(c => c.family == f).map(_.ids(0))
    var result = List[(Int,Identity)]() 
    for(i <- 1 until preCpts.length; if preCpts(i) != postCpts(i)){
      val c1 = postCpts(i); val c1Params = c1.ids
      for(j <- 1 until c1Params.length; if c1.typeMap(j) == f){
        val p = c1Params(j)
        if(!isDistinguished(p) && !ids.contains(p)) result ::= (i, p)
      }
      }
    if(false) println(s"getCrossReferences: $result")
    result
  }

  /** Test whether, if the principal components of cpts1 and cpts2 both have a
    * reference to the same missing component then there is a way of
    * instantiating that component, consistent with the current set of views.
    * @return the identities of all such missing components. */ 
  private def checkCompatibleMissing(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
      : List[MissingCommon]  = {
    require(singleRef)
    //val princ1 = cpts1(0); val princ2 = cpts2(0)
    val missingRefs1 = StateArray.missingRefs(cpts1)
    val missingRefs2 = StateArray.missingRefs(cpts2)
    // The common references considered so far for which there is no way of
    // instantiating the referenced component.
    var missingCommonRefs = List[ProcessIdentity]()
    var missingCommons = List[MissingCommon]()
    for(pid <- missingRefs1; if missingRefs2.contains(pid)){
      val mc = MissingCommon.makeMissingCommon(servers, cpts1, cpts2, pid, views)
      if(mc != null){
// FIXME: if the component c has a reference to one of the present secondary
// components, or vice versa, check that that combination is also possible.
        if(verbose){
          println(s"checkCompatibleMissing($servers, ${StateArray.show(cpts1)},"+
          s" ${StateArray.show(cpts2)})")
          println(s"Failed to find states to instantiate common reference $pid")
        }
        missingCommons ::= mc
      }
    } // end of for loop
    missingCommons
  }

  /** Missing cross references, if singleRef.  For each reference from a
    * component c1 of cpts2 to a component c2 of cpts2, or vice versa, test if
    * sysAbsViews contains the view servers || c1 || c2.  Return all such
    * missing views.  */
  @inline private def missingCrossRefs(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State])
      : List[ComponentView] = {
    assert(singleRef)
    var missing = List[ComponentView]() // missing necessary Views
    for(cptsx <- StateArray.crossRefs(cpts1, cpts2)){
      val cvx = Remapper.mkComponentView(servers, cptsx)
      if(!views.contains(cvx)) missing ::= cvx
    }
    if(verbose && missing.nonEmpty) 
      println(s"missingCrossRefs(${StateArray.show(cpts1)}, "+
        s"${StateArray.show(cpts2)}):\n  $missing")
    missing
  }

  /** If cv completes a delayed transition in effectOnStore, then complete it. */
  def completeDelayed(cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
  = {
    for(nv <- effectOnStore.complete(cv, views)){
      if(verbose) println(s"Adding $nv")
      tryAddView(nv, nextNewViews)
    }
  }

  /** Add mi.nextNewViews to nextNewViews. */
  @inline private 
  def tryAddView(nv: ComponentView, nextNewViews: MyHashSet[ComponentView]) = {
    // require(mi.done); val nv = mi.newView
    if(nextNewViews.add(nv)){
      val (pre, cpts, cv, post, newComponents) = nv.getCreationIngredients
      if(verbose){
        println(s"Adding via completeDelayed $cv -> $nv\n"+
          s"$pre --> $post\n"+
          s"  induces $cv == ${View.show(pre.servers, cpts)}\n"+
          s"  --> ${View.show(post.servers, newComponents)} == $nv")
      }
      if(!nv.representableInScript){
        println("Not enough identities in script to combine transition\n"+
          s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
        sys.exit
      }
    } // end of outer if
  }

  def sanityCheck = effectOnStore.sanityCheck(views)

  def report = effectOnStore.report

}
