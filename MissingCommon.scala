package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.ArrayBuffer
import MissingCommon.Cpts // = Array[State]

/** The representation of the obligation to find a component state c with
  * identity pid = (family,id) such that (1) servers || cpts1(0) || c is in
  * the ViewSet; (2) servers || cpts2(0) || c is in the ViewSet; (3) if c has
  * a reference to a secondary component c2 of cpts1 or cpts2, or vice versa,
  * then servers || c || c2 is in ViewSet (modulo renaming).  This corresponds
  * to condition (c) in the definition of induced transitions with restricted
  * views, for a common missing component with identity pid.  Here cpts1
  * corresponds to the pre-state of a transition, and cpts2 to the view acted
  * upon.
  * 
  * The subclasses differ in the way they represent the missing views.  */
abstract class MissingCommon(
  servers: ServerStates, cpts1: Cpts, /*val cpts2: Cpts,*/ family: Int, id: Int)
{
  import MissingCommon.CptsBuffer // = ArrayBuffer[Cpts]
  import MissingCommon.MissingComponents // = Array[Cpts]
  import MissingCommon.{DoneMask,CountedMask}

  // assert(cpts1.eq(StateArray(cpts1))); assert(cpts2.eq(StateArray(cpts2)))

  /* Overview of main functions.
   * 
   * updateMissingViews       (called from MissingCommonWrapper; in subclasses)
   * 
   * updateWithNewMatch      (called from MissingCommonWrapper)
   * |--updateMissingCandidates (also called from MissingCommonFactory)
   *    |--remapToJoin (in subclasses)
   *    |--updateMissingCandidatesWith (in subclasses)
   * 
   * Other public functions: done, setDone, missingHeads
   * 
   * Used by subclasses: remove, unseen, matches
   */

  @inline protected def pid = (family, id)

  @inline protected def princ1 = cpts1(0)

  require(princ1.processIdentities.contains(pid)) // && 
    // cpts2(0).processIdentities.contains(pid))

  /** Variable encapsulating some flags. */
  private var flags = 0

  /** Is this constraint satisfied? */
  @inline private def isDone = (flags & DoneMask) != 0

  /** Record that this constraint is satisfied. */
  @inline private def setDoneFlag = flags = (flags | DoneMask)

  /** Is this constraint satisfied? */
  @inline def done = synchronized{ isDone }

  /** Record that this is now done.  Also clear data structures to reclaim
    * memory. */
  @inline def setDone: Unit = {
    setDoneFlag; doneMissingCandidates = null; clear
  }

  /** Clear data structures used by subclasses, to reclaim memory. */
  @inline protected def clear: Unit

  /** The result of removing the longest prefix of mc such that views contains
    * the corresponding components, with servers.  Or return null if all are
    * in views. */
  @inline protected def remove(mc: MissingComponents, views: ViewSet)
      : MissingComponents = {
    var i = 0; val len = mc.length
    while(i < len && views.contains(servers, mc(i))) i += 1
    if(i == 0) mc
    else if(i == len) null
    else{
      // Copy mc[i..len) into result
      val result = new Array[Cpts](len-i); var j = 0
      // Inv: result[0..j) = mc[i0..i) where i0 is value of i at start of this
      // stage
      while(i < len){ result(j) = mc(i); j += 1; i += 1 }
      result
    }
  }

  /** Those elements of cptsBuffers such that there is not a corresponding view
    * in views.  The result is sorted.  Pre: the elements of cptsBuffer are
    * those registered with StateArray. */
  @inline protected def unseen(cptsBuffer: ArrayBuffer[Cpts], views: ViewSet)
      : MissingComponents = {
    val missing = new ArrayBuffer[Array[State]] // missing necessary views
    /* Is cpts not already in missing? */
    @inline def isNew(cpts: Array[State]) = {
      var i = 0; val len = missing.length
      // Note: we're using canonical Array[State]s, so reference equality
      while(i < len && missing(i) != cpts) i += 1
      i == len
    }
    var i = 0
    while(i < cptsBuffer.length){
      val cpts = cptsBuffer(i); i += 1
      // assert(StateArray.isCanonical(cpts))
      if(!views.contains(servers, cpts) && isNew(cpts))  missing += cpts
    }
    missing.toArray.sortWith(StateArray.lessThan)
  }


// IMPROVE: move to companion object.

  /** Add `cpts` to `array`, if not a superset of any element there.  Remove any
    * element of `array` that is a proper subset of `cpts`.  Return the
    * resulting array (possibly `array`). */
  @inline protected 
  def addTo(array: Array[MissingComponents], cpts: MissingComponents)
      : Array[MissingComponents] = {
    import MissingCommon.{Eq,Sub,Sup,Inc,compare}
    val len = array.length; val toRetain = new Array[Boolean](len)
    var retainCount = 0; var i = 0; var found = false
    while(i < len){
      // Note: mCpts is local; this is locked; so neither mCpts nor mCpts1 can
      // be mutated by a concurrent thread.
      val mCpts1 = array(i); val cmp = compare(mCpts1, cpts)
      if(cmp != Sup){ toRetain(i) = true; retainCount += 1 }
      found ||= cmp == Sub || cmp == Eq; i += 1
    }
    if(!found || retainCount < array.length){
      val newLen = if(found) retainCount else retainCount+1; assert(newLen > 0)
      val newMC = new Array[MissingComponents](newLen); var j = 0; var i = 0
      while(i < array.length){
        if(toRetain(i)){ newMC(j) = array(i); j += 1 }
        i += 1
      } // end of while
      assert(j == retainCount)
      if(!found) newMC(retainCount) = cpts
      newMC
    } // end of if(!found ...)
    else array // no change
  }

  /** The heads of the missing candidates.  The corresponding MissingInfo should
    * be registered against these in EffectOnStore.mcNotDoneStore.  Defined in
    * subclasses. */
  def missingHeads: Array[Cpts]  

  /** Representation of the States for which
    * MissingCommon.updateMissingCandidates has been executed on this.  State
    * st is represented by st.index+1. */
  private var doneMissingCandidates = new collection.IntSet

  /** Called by MissingCommon.updateMissingCandidates when updating this with
    * st.  Return true if this is the first such instance for st. */
  private def isNewUMCState(st: State): Boolean = {
    assert(st.index >= 0); doneMissingCandidates.add(st.index+1)
  }

  /** States for which the loop of MissingCommon.updateMissingCandidates has
    * been executed, i.e. states instantiating c there. */
  // private val doneMissingCandidatesRenamed: HashSet[State] = null
  //  IMPROVE: not used at present

  /** Called by MissingCommon.updateMissingCandidates when updating this with
    * st.  Return true if this is the first such instance for st instantiating
    * c.  Not currently used. */
  private def isNewUMCRenamedState(st: State): Boolean = ???
  // doneMissingCandidatesRenamed.add(st)

  /** Is cv a possible match to clause (1), i.e. does it match servers ||
    * cpts1(0) || c? */
  @inline protected def matches(cv: ComponentView) = synchronized{
    cv.servers == servers && cv.components(0) == princ1
  }
  // IMPROVE: can we also ensure that cv.components(1).processIdentity == pid?

  /** Update missingCandidates to include lists of missing components
    * corresponding to instantiating the missing component with c.  Add to cb
    * the components that this needs to be registered against in the
    * EffectOnStore, namely missingHeads.  Return true if this is now
    * done.  */
  protected 
  def updateMissingCandidatesWith(c: State, views: ViewSet, cb: CptsBuffer)
      : Boolean 

  /** All relevant renamings of cpt1 as a possible instantiation of the common
    * missing component.  Identity on params of servers and princ1, but
    * otherwise mapping to parameters of a secondary component c2 of cpts1 or
    * cpts2 only if there is already a cross reference between cpt1 and c2 (in
    * either direction).  Defined in subclasses; but (TODO) ignoring secondary
    * components of cpts2 in TwoStepMissingCommon.  */
  protected def remapToJoin(cpt1: State) : Array[State]//  = 
    // Unification.remapToJoin(servers, princ1, cpts1, cpts2, cpt1)

  /** Update missingCandidates to include lists of missing components
    * corresponding to instantiating c with a renaming of cpt1.  Add to vb the
    * views that this needs to be registered against in the EffectOnStore,
    * namely missingHeads.
    * 
    * Pre: views contains a view servers || cpts1(0) || cpt1 to
    * instantiate clause (1) of this.
    * 
    * @return true if this is now complete. */
  def updateMissingCandidates(cpt1: State, views: ViewSet, vb: CptsBuffer)
      : Boolean = {
    require(!done && cpt1.hasPID(family,id))
    if(isNewUMCState(cpt1)){
      // All relevant renamings of cpt1: identity on params of servers and
      // princ1, but otherwise either to other params of cpts1 or cpts2, or to
      // fresh values.  
      val renames = remapToJoin(cpt1); var i = 0; var found = false
      while(i < renames.length && !found){
        val c = renames(i); i += 1
        if(true || isNewUMCRenamedState(c)){ // IMPROVE
          if(updateMissingCandidatesWith(c, views, vb)) found = true
        }
      } // end of while loop
// IMPROVE: can we do all the updateMissingCandidatesWith updates together?  
// Each copies the arrays.
      found
    } // end of if isNewUMCState
    else{ 
      // This update has previously been done, but we might need to
      // re-register the MissingInfo object, because of sharing.  The
      // following might be a bit pessimistic.  IMPROVE: store the relevant
      // values from one instance to reuse in the next.
// IMPROVE: I think the commented-out code is better, but needs to deal with the
// case that vb1 is null.  
/*    val vb1 = updateMissingViews(views); assert(vb1 != null, this)
      vb ++= vb1  */
      for(cpts <- missingHeads) if(!views.contains(servers, cpts)) vb += cpts
      false
    }
  }

  /** Update this based on using cv to instantiate servers || princ1 || c.
    * @return a CptsBuffer containing those Views against which this needs to
    * be registered, namely missingHeads; or null if this is done. */
  def updateWithNewMatch(cv: ComponentView, views: ViewSet)
      : CptsBuffer = synchronized{
    require(matches(cv))
    // if(highlight) println(s"updateWithNewMatch($cv) $pid")
    if(!done){
      val cpt1 = cv.components(1); val vb = new CptsBuffer
      if(cpt1.hasPID(family,id)){
        // Remap cpt1 to a normal form.  This avoids repeating work for
        // equivalent states within updateMissingCandidates.
        // val cpt1Norm =  Remapper.remapWRT(servers, cpts1, cpts2, cpt1)
        // I think the following is sound.  If so, simplify remapWRT
        // val cpt1Norm = Remapper.remapWRT(servers, Array(princ1), Array(), cpt1)
        // assert(cpt1 == cpt1Norm, s"servers = $servers;\n"+
        //     s"princ1 = $princ1; cpt1 = $cpt1; cpt1Norm = $cpt1Norm")
        if(updateMissingCandidates(cpt1, views, vb)){ 
          //log(MissingCommon.UpdateWithNewMatchSuccess(cv, ply))
          setDone; null
        }
        else vb
      }
      else vb
    }
    else null
  }

  /** Update missingCandidates based on views.  Remove elements of views from
    * the front of each.  If any is now empty, then mark this as satisfied.
    * Return views against which this should now be registered, or null if
    * done. */
  def updateMissingViews(views: ViewSet): CptsBuffer
}

// =======================================================

object MissingCommon{
  /* Overview of main functions.
   * 
   * makeMissingCommon          (called from EffectOn)
   * |--getOrInit
   * |--(companion).updateMissingCandidates 
   */

  /** The states of some components. */
  type Cpts = Array[State]

  /** A buffer for storing Cpts, against which a MissingInfo should be
    * registered in the EffectOnStore (with appropriate servers). */
  type CptsBuffer = ArrayBuffer[Cpts]

  /** Each value cands of type MissingComponents represents that if
    * (servers,cpts) is added to the ViewSet for each cpts in cands, then this
    * obligation will be discharged.  Each corresponds to a particular
    * component state c for which condition (1) is satisfied; cands contains
    * those components corresponding to conditions (2) and (3).  The list is
    * sorted (wrt StateArray.lessThan).  */
  type MissingComponents = Array[Cpts]

  def showMissingComponents(mc: MissingComponents) = 
    mc.map(StateArray.show).mkString("; ")

  /** Bit masks used for extracting state from the `flags` of a
    * MissingCommon. */
  val DoneMask = 1

  val CountedMask = 2

  /** For a MissingCommon corresponding to servers, cpts1 and cpts2, given that
    * c is a component with identity pid that satisfies condition (1), find
    * those components that are required for conditions (2) and (3).  Here
    * cpts1 corresponds to the pre-state of a transition, and cpts2 to the
    * view acted upon.  Uses values registered in StateArray. */
// IMPROVE: seems to include value for condition (1)
  @inline def requiredCpts(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State], c: State)
      : ArrayBuffer[Array[State]] = {
    val ab = new ArrayBuffer[Array[State]]
    // IMPROVE: do we need (cpts1(0), c)?  (We do in Debugger.)
    getRequiredCpts(servers, cpts1, c, ab)
    getRequiredCpts(servers, cpts2, c, ab)
    ab
  } 

  /** Add (servers,cpts) (remapped) to ab. */
  @inline private
  def add1(servers: ServerStates, cpts: Array[State], ab: ArrayBuffer[Cpts]) =
    ab += Remapper.remapComponents(servers, cpts)

  /** Those components that are required for common missing references to
    * component c to/from cpts.  (1) From cpts(0) to c; (2) possibly from c to
    * a secondary component of cpts; (3) possibly from a secondary component
    * of cpts to c.  Add each to ab. */
  @inline private def getRequiredCpts(
    servers: ServerStates, cpts: Cpts, c: State, ab: ArrayBuffer[Cpts]) 
  = {
    @inline def add(cpts: Array[State]): Unit = // add1(servers, cpts1, ab)
     ab += Remapper.remapComponents(servers, cpts)
// FIXME: change name

    add(Array(cpts(0), c))
    // add1(servers, Array(cpts(0), c), ab)
    // getRequiredSecondaryCpts(servers, cpts, c, ab)
    var j = 1
    // Condition (3): refs from c to components of cpts
    while(j < c.length){
      if(c.includeParam(j)){
        // Does c's jth parameter reference an element c1 of cpts?
        val c1 = StateArray.find(c.processIdentities(j), cpts);
        if(c1 != null) add(Array(c, c1))
      }
      j += 1
    }
    // Does any component of cpts reference c?
    val (ct,cid) = c.componentProcessIdentity; j = 1
    while(j < cpts.length){
      val c1 = cpts(j); j += 1; 
      if(c1.hasIncludedParam(ct, cid)) add(Array(c1, c))
    }
  }

  /** Get the first set of required components for a TwoStepMissingCommon. */
  def getRequiredCptsTwoStep1(
    servers: ServerStates, cpts1: Cpts, princ2: State, c: State)
      : ArrayBuffer[Array[State]] = {
    val ab = new ArrayBuffer[Array[State]]
    add1(servers, Array(cpts1(0), c), ab)
    add1(servers, Array(princ2, c), ab)
    getRequiredSecondaryCpts(servers, cpts1, c, ab)
    ab
  }

  /** Get the second set of required components for a TwoStepMissingCommon. */
  def getRequiredCptsTwoStep2(servers: ServerStates, cpts2: Cpts, c: State)
      : ArrayBuffer[Array[State]] = {
    // Note: this possible includes the components corresponding to c having a
    // reference to cpts2(0) (principal of the view). 
    val ab = new ArrayBuffer[Array[State]]
    getRequiredSecondaryCpts(servers, cpts2, c, ab)
    ab
  }

  /** Find required components for secondary components, and add to ab: possibly
    * from c to a secondary component of cpts; and possibly from a secondary
    * component of cpts to c. */ 
  @inline private def getRequiredSecondaryCpts(
    servers: ServerStates, cpts: Cpts, c: State, ab: ArrayBuffer[Cpts]) 
  = {
    var j = 1
    // Condition (3): refs from c to components of cpts
    while(j < c.length){
      if(c.includeParam(j)){
        // Does c's jth parameter reference an element c1 of cpts?
        val c1 = StateArray.find(c.processIdentities(j), cpts);
        if(c1 != null) add1(servers, Array(c, c1), ab)
      }
      j += 1
    }
    // Does any component of cpts reference c?
    val (ct,cid) = c.componentProcessIdentity; j = 1
    while(j < cpts.length){
      val c1 = cpts(j); j += 1; 
      if(c1.hasIncludedParam(ct, cid)) add1(servers, Array(c1, c), ab)
    }
  }

  /** Those components that are required for common missing references to
    * component c to/from cpts.  (1) From cpts(0) to c; (2) possibly from c to
    * a secondary component of cpts; (3) possibly from a secondary component
    * of cpts to c.   */
  @inline def getRequiredCpts(servers: ServerStates, cpts: Cpts, c: State)
      : ArrayBuffer[Cpts] = {
    val ab = new ArrayBuffer[Cpts]; getRequiredCpts(servers, cpts, c, ab); ab
  }

  // Possible returns from compare
  val Eq = 0; val Sub = 1; 
  val Sup = 2; val Inc = 4

  /** Compare mc1 and mc2.  Return Eq is equal, Sub if mc1 is proper subset, Sup
    * if mc1 is a proper superset, and Inc if they are incomparable.  Pre:
    * both are sorted.  Requires that neither is mutated concurrently. */
  @inline  
  def compare(mc1: MissingComponents, mc2: MissingComponents): Int = {
    var i1 = 0; var i2 = 0; var sub = true; var sup = true
    // Inv sub is true if elements of mc1 seen so far are all in mc2; sup is
    // true if elements of mc2 seen so far are all in mc1.  Still need to
    // compare from indices i1 and i2 onwards.
    while(i1 < mc1.length && i2 < mc2.length && (sub || sup)){
      val comp = StateArray.compare(mc1(i1), mc2(i2))
      if(comp < 0){ sub = false; i1 += 1 } // c1.head not in mc2
      else if(comp == 0){ i1 += 1; i2 += 1 }
      else{ sup = false; i2 += 1 } // c2.head is not in mc1
    }
    sub &&= (i1 == mc1.length); sup &&= (i2 == mc2.length)
    if(sub){ if(sup) Eq else Sub } else if(sup) Sup else Inc
  }

  /** Is mCpts1 a subset of mCpts2? */
  @inline private 
  def subset(mCpts1: MissingComponents, mCpts2: MissingComponents): Boolean = {
    // We use the fact that each MissingComponents is sorted, and
    // Array[State]s are registered with tateArray, so we can use reference
    // equality.
    var i1 = 0; var i2 = 0; val len1 = mCpts1.length; val len2 = mCpts2.length
    var subset = true
    // Inv: subset is true if mCpts1[0..len1) is a subset of mCpts2.  
    while(i1 < len1 && subset){
      val cpts1 = mCpts1(i1); i1 += 1
      // Test if cpts1 in mCpts2
      while(i2 < len2 && mCpts2(i2) != cpts1) i2 += 1
      // IMPROVE: bail out if len1-i1 >= len2-i2 (?)
      subset = i2 < len2; i2 += 1
    }
    subset
  }

  // Events for log 
  trait MCEvent
  /** A call to add, leading to missingComponents being set to mc. */
  case class AddMC(mc: MissingComponents) extends MCEvent{
    override def toString = "AddMC"+showMissingComponents(mc)+")"
  }
  /** A call to removeViews(mc) giving result mc1. */
  case class UpdateMC(mc: MissingComponents, mc1: MissingComponents, ply: Int)
      extends MCEvent{
    override def toString = 
      "UpdateMC(mc = "+showMissingComponents(mc)+
        "; mc1 = "+showMissingComponents(mc1)+s"; ply = $ply)"
  }
  /** A call to setDone. */
  case object SetDoneMC extends MCEvent

  /** A call to updateMissingCandidates(cpt1), where instantiating with c led to
    * this becoming done. */
  case class MissingCandidateSuccess(cpt1: State, c: State) extends MCEvent

  /** A call to updateWithNewMatch(cv) was successful. */
  case class UpdateWithNewMatchSuccess(cv: ComponentView, ply: Int)
      extends MCEvent

  /** A call to updateWithNewMatch(cv,...,key). */
  case class UpdateWithNewMatch(cv: ComponentView, key: (ServerStates,State)) 
      extends MCEvent

  /** A repeated call to updateMissingCandidates(cpt1). */
  case class UMCRepeat(cpt1: State) extends MCEvent
}
