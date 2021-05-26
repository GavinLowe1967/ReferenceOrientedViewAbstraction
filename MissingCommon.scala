package ViewAbstraction

import ViewAbstraction.RemapperP.{Remapper,Unification}
import ox.gavin.profiling.Profiler
import scala.collection.mutable.ArrayBuffer

/** The representation of the obligation to find a component state c with
  * identity pid such that (1) servers || cpts1(0) || c is in the ViewSet; (2)
  * servers || cpts2(0) || c is in the ViewSet; (3) if c has a reference to a
  * secondary component c2 of cpts1 or cpts2, then servers || c || c2 is in
  * ViewSet (modulo renaming).  This corresponds to case 2 on p. 113 of the
  * notebook. */
class MissingCommon(
    val servers: ServerStates, val cpts1: Array[State], val cpts2: Array[State],
    val pid: ProcessIdentity){
  val princ1 = cpts1(0)

  require(princ1.processIdentities.contains(pid) && 
    cpts2(0).processIdentities.contains(pid))

  /** Each value cands of type MissingCandidates represents that if all the
    * elements of cands are added to the ViewSet, then this obligation will be
    * discharged. */
  type MissingCandidates = List[ComponentView]

  /** When any element of missingCandidates is satisfied, then this obligation
    * will be discharged. */
  var missingCandidates = List[MissingCandidates]()

  private var isDone = false

  /** Is this constraint satisfied? */
  @inline def done = isDone

  /** Update missingCandidates based on the addition of cv.  Remove cv from
    * each; if any is now empty, then mark this as satisfied and return
    * true. */
  def updateMissingViews(cv: ComponentView): Boolean = {
    var mcs = missingCandidates; missingCandidates = List()
    while(mcs.nonEmpty){
      var mc = mcs.head; mcs = mcs.tail; var newMc = List[ComponentView]()
      // Remove cv from mc; add resulting list to missingCandidates
      while(mc.nonEmpty){
        val cv1 = mc.head; mc = mc.tail
        if(cv1 != cv) newMc ::= cv1 
      }
      if(newMc.isEmpty) isDone = true
      else missingCandidates ::= newMc
    }
    done
  }

  /** Is cv a possible match to clause (1), i.e. does it match servers ||
    * cpts1(0) || c? */
  def matches(cv: ComponentView) = 
    cv.servers == servers && cv.components(0) == princ1
  // IMPROVE: can we also ensure that cv.components(1).processIdentity == pid?

  import MissingCommon.ViewBuffer

  /** Update this based on using cv to instantiate servers || princ1 || c.
    * Add to vb those Views against which this needs to be registered. */
  def updateMissingCommon(cv: ComponentView, views: ViewSet, vb: ViewBuffer)
      : Boolean = {
    require(matches(cv)); val cpt1 = cv.components(1) 
    if(cpt1.hasPID(pid)){
      // val oldMissingCandidates = missingCandidates
      if(MissingCommon.updateMissingCandidates(this, cpt1, views, vb)){
        // println(s"updateMC($cv):\n  $this\nCompleted!")
        isDone = true
      }
      // if(missingCandidates != oldMissingCandidates){
      //   // Should have added at the front
      //   val lenDiff = missingCandidates.length - oldMissingCandidates.length
      //   assert(missingCandidates.drop(lenDiff) == oldMissingCandidates)
      // }
    }
    isDone
  }

  def allCandidates: List[ComponentView] = missingCandidates.flatten.distinct

  /** Sanity check that no elements of views remain in missingCandidates. */
  def sanityCheck(views: ViewSet) = {
    assert(!done)
    for(mcs <- missingCandidates; v <- mcs) assert(!views.contains(v))
  }

  override def toString = 
    s"MissingCommon($servers, ${StateArray.show(cpts1)},"+
      s"  ${StateArray.show(cpts2)}, $pid)"
}


// =======================================================

object MissingCommon{
  /** A buffer for storing Views, against which a MissingInfo should be
    * registered in the EffectOnStore. */
  type ViewBuffer = ArrayBuffer[ComponentView]


  /** A MissingCommon object, corresponding to servers, cpts1, cpts2 and pid, or
    * null if the obligation is already satisfied.
    * 
    * For each component state c with identity pid such that servers ||
    * cpts1(0) || c is in views, missingCandidates contains the list of Views
    * that are needed to satisfy the obligation but are currently missing from
    * views: (1) servers || cpts2(0) || c; and (2) if c has a reference to a
    * secondary component c2 of cpts1 or cpts2, then servers || c || c2
    * (renamed).
    */
  def makeMissingCommon(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State], 
    pid: ProcessIdentity, views: ViewSet)
      : MissingCommon = {
    Profiler.count("makeMissingCommon")
    assert(singleRef)
    // assert(cpts1.length == 2, StateArray.show(cpts1)) // not true
    assert(cpts2.length == 2, StateArray.show(cpts2))
    val princ1 = cpts1(0); val princ2 = cpts2(0); var found = false
    val mc = new MissingCommon(servers, cpts1, cpts2, pid)
    val ab = new ViewBuffer
    // All elements of views of the form servers || princ1 || c where c has
    // identity pid
    var matches = matchesFor(servers, princ1, pid, views)
    while(matches.nonEmpty && !found){
      val cv1 = matches.head; matches = matches.tail
      found = updateMissingCandidates(mc, cv1.components(1), views, ab)
    } // end of while loop
    // Profiler.count("MissingCandidateSize"+mc.allCandidates.length)
    if(found) null else mc 
    // Note: we don't need to do anything with ab here, as mc.allcandidates
    // will store the same Views.  IMPROVE?
  }

  /** Update mc.missingCandidates to include lists of missing views
    * corresponding to instantiating c with a renaming of cpt1.  Add to vb the
    * views that mc needs to be registered against in the EffectOnStore.
    * @return true if mc is now complete. */
  @inline private 
  def updateMissingCandidates(
    mc: MissingCommon, cpt1: State, views: ViewSet, vb: ViewBuffer)
      : Boolean = {
    require(cpt1.hasPID(mc.pid))
    // All relevant renamings of cpt1: identity on params of servers and
    // princ1, but otherwise either to other params of cpts2 or to fresh
    // values.
// FIXME: also rename to other params of cpts1?
    val renames = Unification.remapToJoin(mc.servers, mc.princ1, mc.cpts2, cpt1)
    var i = 0; var found = false
    while(i < renames.length && !found){
      val c = renames(i); i += 1
      val missing = getMissingCandidates(mc, c, views, vb)
      if(missing.isEmpty) found = true
      else mc.missingCandidates ::= missing
    } // end of while loop
    found
  }

  /** Find the missing Views that are necessary to complete mc for a particular
    * candidate state c.  Return a list containing each of the following that
    * is not currently in views: (1) servers || cpts2(0) || c; and (2) if c
    * has a reference to a secondary component c2 of cpts1 or cpts2, then
    * servers || c || c2 (renamed).  Add to vb the views that mc needs to be
    * registered against in the EffectOnStore.*/
  @inline private 
  def getMissingCandidates(
    mc: MissingCommon, c: State, views: ViewSet, vb: ViewBuffer)
      : List[ComponentView] = {
    var missing = List[ComponentView]() // missing necessary views
    val servers = mc.servers; val cpts1 = mc.cpts1; val cpts2 = mc.cpts2
    // Add servers || cptsx, if not in views
    @inline def maybeAdd(cptsx: Array[State]) = { 
      val cvx = Remapper.mkComponentView(servers, cptsx)
      if(!views.contains(cvx)){ missing ::= cvx; vb += cvx }
    }

    maybeAdd(Array(cpts2(0), c))
    // If c has a reference to a secondary component c2 of cpts2 or cpts1,
    // then the View servers || c || c2 is necessary.
    var j = 1
    while(j < c.length){
      val pid2 = c.processIdentities(j); j += 1
      val c2 = StateArray.find(pid2, cpts2)
      if(c2 != null) maybeAdd(Array(c, c2))
      val c1 = StateArray.find(pid2, cpts1)
      if(c1 != null) maybeAdd(Array(c, c1))
    }
    missing
  }

  /** All elements of views of the form servers || princ || c where c has
    * identity pid. */
  @inline private def matchesFor(
    servers: ServerStates, princ: State, pid: ProcessIdentity, views: ViewSet)
      : List[ComponentView] = {
    var result = List[ComponentView]()
    val iter = views.iterator(servers, princ)
    while(iter.hasNext){
      val cv = iter.next; val cpts = cv.components; assert(cpts.length == 2, cv)
      if(cpts(1).hasPID(pid)) result ::= cv
    }
    result
  }

}
