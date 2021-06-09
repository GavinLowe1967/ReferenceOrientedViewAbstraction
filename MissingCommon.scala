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
  private var missingCandidates = List[MissingCandidates]()

  private var isDone = false

  /** Is this constraint satisfied? */
  @inline def done = isDone

  /** The heads of the missing candidates.  The corresponding MissingInfo should
    * be registered against these in
    * EffectOnStore.mcMissingCandidatesStore. */
  def missingHeads = missingCandidates.map(_.head)

  /** Update mc based on the addition of cv.  If cv matches mc.head, remove it,
    * and the maximal prefix from views.  If then done, record this.
    * Otherwise add to toRegister the next view, against which this should be
    * registered. */
  private def updateMissingCandidates(mc: MissingCandidates, cv: ComponentView, 
    views: ViewSet, toRegister: ArrayBuffer[ComponentView])
      : MissingCandidates = {
    if(mc.head == cv){
      var mc1 = mc
      while(mc1.nonEmpty && views.contains(mc1.head)) mc1 = mc1.tail
      if(mc1.isEmpty) isDone = true
      else toRegister += mc1.head
      mc1
    }
    else mc
  }

  /** Update missingCandidates based on the addition of cv.  Remove cv from
    * each; if any is now empty, then mark this as satisfied.  Return views
    * against which this should now be registered, or null if done. */
  def updateMissingViews(cv: ComponentView, views: ViewSet)
      : ArrayBuffer[ComponentView] = {
    val toRegister = new ArrayBuffer[ComponentView]
    missingCandidates = 
      missingCandidates.map(mc => 
        updateMissingCandidates(mc, cv, views, toRegister))
    if(done) null 
    else{ 
      assert(toRegister.nonEmpty,
        s"updateMissingViews($cv) with\n${missingCandidates.mkString("\n")}")
      toRegister
    }
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
    if(cpt1.hasPID(pid))
      if(MissingCommon.updateMissingCandidates(this, cpt1, views, vb))
        isDone = true
    isDone
  }

  /** Sanity check that no head element of missingCandidates is in views. */
  def sanityCheck(views: ViewSet) = {
    assert(!done)
    for(mcs <- missingCandidates){ 
      val v = mcs.head
      assert(!views.contains(v), this.toString+" still contains "+v)
    }
  }

  override def toString = 
    s"MissingCommon($servers, ${StateArray.show(cpts1)},"+
      s"  ${StateArray.show(cpts2)}, $pid)"

  /** Equality test.  The constraint this represents is logically captured by
    * its initial parameters, so we use equality of parameters as the notion
    * of equality. */
  override def equals(that: Any) = that match{
    case mc: MissingCommon =>
      mc.hashCode == hashCode && // optimisation
      mc.servers == servers && mc.cpts1.sameElements(cpts1) &&
      mc.cpts2.sameElements(cpts2) && mc.pid == pid
    case null => false
  }

  /** Hash code, based on the same principle as equality. */
  override val hashCode = {
    @inline def f(x:Int, y: Int) = x*97+y
    f(f(f(f(servers.hashCode, StateArray.mkHash(cpts1)), 
      StateArray.mkHash(cpts2)), pid._1), pid._2)
  }

  /** Ordering on MissingCommon values.  Return a value x s.t.: x < 0 if this <
    * that; x == 0 when this == that; x > 0 when this > that. */
  def compare(that: MissingCommon) = {
    val hashComp = compareHash(hashCode, that.hashCode)
    if(hashComp != 0) hashComp
    else{
      val ssComp = servers.compare(that.servers)
      if(ssComp != 0) ssComp
      else{
        val cmp1 = StateArray.compare(cpts1, that.cpts1)
        if(cmp1 != 0) cmp1
        else{
          val cmp2 = StateArray.compare(cpts2, that.cpts2)
          if(cmp2 != 0) cmp2
          else{
            val familyDiff = pid._1 - that.pid._1
            if(familyDiff != 0) familyDiff
            else pid._2 - that.pid._2
          }
        }
      }
    }
  }

  /** A measure of the size of this: the number of ComponentViews stored. */
  def size = missingCandidates.map(_.length).sum
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
    assert(cpts2.length == 2, StateArray.show(cpts2))
    val princ1 = cpts1(0); val princ2 = cpts2(0); var found = false
    val mc = new MissingCommon(servers, cpts1, cpts2, pid)
    val ab = new ViewBuffer
    // Search for elements of views of the form servers || princ1 || c where c
    // has identity pid
    val iter = views.iterator(servers, princ1)
    while(iter.hasNext && !found){
      val cv = iter.next; val cpts = cv.components; assert(cpts.length == 2, cv)
      val cpt1 = cpts(1)
      if(cpt1.hasPID(pid)) found = updateMissingCandidates(mc, cpt1, views, ab)
    }
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
      val missing = getMissingCandidates(mc, c, views) 
      if(missing.isEmpty) found = true
      else{ mc.missingCandidates ::= missing; vb += missing.head }
    } // end of while loop
    found
  }

  /** Find the missing Views that are necessary to complete mc for a particular
    * candidate state c.  Return a list containing each of the following that
    * is not currently in views: (1) servers || cpts2(0) || c; and (2) if c
    * has a reference to a secondary component c2 of cpts1 or cpts2, then
    * servers || c || c2 (renamed). */
  @inline private 
  def getMissingCandidates(mc: MissingCommon, c: State, views: ViewSet)
      : List[ComponentView] = {
    var missing = List[ComponentView]() // missing necessary views
    val servers = mc.servers; val cpts1 = mc.cpts1; val cpts2 = mc.cpts2
    // Add servers || cptsx, if not in views
    @inline def maybeAdd(cptsx: Array[State]) = { 
      val cvx = Remapper.mkComponentView(servers, cptsx)
      if(!views.contains(cvx)){ missing ::= cvx /*; vb += cvx */ }
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


}
