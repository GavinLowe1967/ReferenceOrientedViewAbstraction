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
  * upon. */
abstract class MissingCommon{
  import MissingCommon.CptsBuffer // = ArrayBuffer[Cpts]

  import MissingCommon.MissingComponents // = Array[Cpts]

  val servers: ServerStates 
  //val cpts1: Cpts
  //val cpts2: Cpts
  //val family: Int
  //val id: Int

  import MissingCommon.{DoneMask,CountedMask}

  /** Variable encapsulating some flags. */
  private var flags = 0

  /** Is this constraint satisfied? */
  @inline private def isDone = (flags & DoneMask) != 0

  /** Record that this constraint is satisfied. */
  @inline protected def setDoneFlag = flags = (flags | DoneMask)

  /** Is this constraint satisfied? */
  @inline def done = synchronized{ isDone }

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

  /** The heads of the missing candidates.  The corresponding MissingInfo should
    * be registered against these in EffectOnStore.mcNotDoneStore. */
  def missingHeads: Array[Cpts]  

  /** Update this based on using cv to instantiate servers || princ1 || c.
    * @return a CptsBuffer containing those Views against which this needs to
    * be registered, namely missingHeads; or null if this is done. */
  def updateWithNewMatch(cv: ComponentView, views: ViewSet)
      : CptsBuffer

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
  @inline def requiredCpts(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State], c: State)
      : ArrayBuffer[Array[State]] = {
    val ab = new ArrayBuffer[Array[State]]
    getRequiredCpts(servers, cpts1, c, ab)
    getRequiredCpts(servers, cpts2, c, ab)
    ab
/*
    /* Add the normalised version of cpts to ab. */
    @inline def add(cpts: Array[State]) = {
      // ComponentView0.checkValid(servers, cpts) // IMPROVE
      ab += Remapper.remapComponents(servers, cpts)
    }
    // Condition (2)
    add(Array(cpts2(0), c)); var j = 1
    // Condition (3): refs from c to components of cpts1 or cpts2
    while(j < c.length){
      if(c.includeParam(j)){
        val pid2 = c.processIdentities(j)
        val c2 = StateArray.find(pid2, cpts2); if(c2 != null) add(Array(c, c2))
        val c1 = StateArray.find(pid2, cpts1); if(c1 != null) add(Array(c, c1))
      }
      j += 1
    }
    // Note: the following corresponds to references from secondary components
    // of cpts1 or cpts2 to c, which is a new clause in condition (c).
    val (ct,cid) = c.componentProcessIdentity; j = 1
    while(j < cpts1.length){
      val c1 = cpts1(j); j += 1; 
      if(c1.hasIncludedParam(ct, cid)) add(Array(c1, c))
    }
    j = 1
    while(j < cpts2.length){
      val c2 = cpts2(j); j += 1; 
      if(c2.hasIncludedParam(ct, cid)) add(Array(c2, c))
    }
    Profiler.count("MissingCommon.requiredCpts "+ab.length)
    ab
 */
  } 

  /** Those components that are required for common missing references to
    * component c to/from cpts.  (1) From cpts(0) to c; (2) possibly from c to
    * a secondary component of cpts; (3) possibly from a secondary component
    * of cpts to c.  Add each to ab. */
  @inline private def getRequiredCpts(
    servers: ServerStates, cpts: Cpts, c: State, ab: ArrayBuffer[Cpts]) 
  = {
    @inline def add(cpts: Array[State]) = 
      ab += Remapper.remapComponents(servers, cpts)

    add(Array(cpts(0), c))
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
