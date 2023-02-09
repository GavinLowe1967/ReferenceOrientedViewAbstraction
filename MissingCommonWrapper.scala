package ViewAbstraction

import scala.collection.mutable.ArrayBuffer
import ox.gavin.profiling.Profiler

import RemapperP.Remapper

/** Representation of an instance of condition (c).  The induced transition is
  * described by `inducedTrans`.  The common missing identities are
  * `commonMissingPids. */
class MissingCommonWrapper(
  val inducedTrans: InducedTransitionInfo,
  val commonMissingPids: Array[ProcessIdentity]
){
  require(inducedTrans.cpts != null /* && commonMissingPids.nonEmpty */)
  // commonMissingPids should be sorted
  import MissingCommonWrapper.lessThan
  for(i <- 0 until commonMissingPids.length-1) 
    require(lessThan(commonMissingPids(i), commonMissingPids(i+1)), 
      commonMissingPids(i).toString+"; "+commonMissingPids(i+1))

  def servers = inducedTrans.servers

  def prePrincipal = inducedTrans.prePrincipal

  @inline def isNewViewFound(views: ViewSet) = inducedTrans.isNewViewFound(views)

  /** Index into commonMissingPids. */
  private var pidsIndex = 0

  /** Has this been superseded by another MissingCommonWrapper with the same
    * newView, servers, preCpts, cpts, and a subset of the
    * commonMissingPids? */
  // private var superseded = false

  // def isSuperseded: Boolean = synchronized{ superseded }

  // def setSuperseded: Unit = synchronized{ superseded = true }

  import MissingCommonWrapper.{Cpts,CptsBuffer}
  // Array[State], Iterable[Cpts], resp

  /** The current MissingCommon.  Corresponds to
    * commonMissingPids(pidsIndex). */
  private var mc: MissingCommon = null

  def missingHeads: Array[ReducedComponentView] = 
    mc.missingHeads.map(cpts => ReducedComponentView(servers, cpts))

  def done = mc == null

  // /** Result returned by operations that update this: the components against
  //   * which this should be registered. */
  // type CptsBuffer = Iterable[Cpts]

  /** Update the missingCandidates of the current MissingCommon based on views.
    * Remove elements of views from the front of each.  If any is now empty,
    * then the MissingCommon is satisfied.  Return views against which this
    * should now be registered, or null if done. */
  def updateMissingViews(views: ViewSet): CptsBuffer = synchronized{
    val buff = mc.updateMissingViews(views)
    if(buff == null) advance1(views) else buff
  }

  /** Update the current MissingCommon based on using cv to instantiate servers
    * || princ1 || c.
    * @return a CptsBuffer containing those Views against which this needs to
    * be registered, namely missingHeads; or null if this is now done. */
  def updateWithNewMatch(cv: ComponentView, views: ViewSet)
      : CptsBuffer = synchronized{
    require(!done)
    val buff = mc.updateWithNewMatch(cv, views)
    if(buff == null) advance1(views) else buff
  }

  /** Advance to the next common missing identity, and initialise the
    * corresponding CommonMissing.  Return the views against which this should
    * now be registered, or null if this is now done. */
  @inline private def advance1(views: ViewSet): CptsBuffer = {
    require(mc.done); pidsIndex += 1; advance(views)
    if(mc != null) mc.missingHeads else null 
  }


  /** Initialise the MissingCommon for the next common missing process identity,
    * if any.  If all are done, set mc = null.  */
  @inline private def advance(views: ViewSet) = {
    var done = false 
    // done = true if we've created an new MissingCommon
    while(pidsIndex < commonMissingPids.length && !done){
      val pid = commonMissingPids(pidsIndex)
      val newMC = MissingCommonFactory.makeMissingCommon(
        inducedTrans.servers, inducedTrans.preCpts, inducedTrans.cpts, 
        pid, views, !useTwoStepMC)
// IMPROVE: don't use TwoStep after first iteration
      if(newMC == null) pidsIndex += 1 else{ mc = newMC; done = true }
    }
    if(!done) mc = null
  }

  /** Initialise this based on views. */
  def init(views: ViewSet) = advance(views)

}

// ==================================================================

object MissingCommonWrapper{
  // Do we use two-step missing commons? 
  // val UseTwoStep = true

  type Cpts = Array[State]

  /** Result returned by operations that update a MissingCommonWrapper: the
    * components against which it should be registered. */
  type CptsBuffer = Iterable[Cpts]

  /** Produce a MissingCommonWrapper corresponding to inducedTrans and
    * commonMissingPids.  Can return null to indicate all required views are
    * in `views`. */ 
  def apply(inducedTrans: InducedTransitionInfo, views: ViewSet)
    // commonMissingPids: Array[ProcessIdentity], 
      : MissingCommonWrapper = {
    val commonMissingPids = inducedTrans.commonMissingRefs
    if(commonMissingPids.isEmpty)  
      null // shortcut  IMPROVE (can't return null)
    else{
      // IMPROVE: avoid creating the MCW
      val pids1 = commonMissingPids.distinct.sortWith(lessThan)
      val mcw = new MissingCommonWrapper(inducedTrans, pids1)
      val missingHeads = mcw.init(views)
      // If done, or implied by an existing mcw, return null.
      mcw
    //   if(mcw.done) mcw else if(addToStore(mcw)) mcw 
    //   else{ 
    //     // println("returning null"); 
    //     Profiler.count("MissingCommonWrapper subsumed."); null }
    }
  }

  /** Is condition C satisfied? */
  def conditionCSatisfied(inducedTrans: InducedTransitionInfo, views: ViewSet)
      : Boolean = {
    // IMPROVE: avoid creating MCW object
    val commonMissingPids = inducedTrans.commonMissingRefs
    if(commonMissingPids.isEmpty) true // shortcut
    else{
      val pids1 = commonMissingPids.distinct.sortWith(lessThan)
      val mcw = new MissingCommonWrapper(inducedTrans, pids1)
      val missingHeads = mcw.init(views)
      mcw.done
    }
  }

  /** Ordering on ProcessIdentity. */
  def lessThan(pid1: ProcessIdentity, pid2: ProcessIdentity) = 
    pid1._1 < pid2._1 || pid1._1 == pid2._1 && pid1._2 < pid2._2

  import SingleRefEffectOnUnification.commonMissingRefs


  /* Possible return values from compareCMPids. */
  private val Equal = 0; private val Subset = 1; 
  private val Superset = 2; private val Incomparable = 3

  /** Compare the remaining commonMissingPids of mcw1 and mcw2.  Return Equal,
    * Subset, Supset, Incomparable if those of mcw1 and equal to, a subset of,
    * a superset of, or incomparable to those of mcw2, respectively.  */ 
  private 
  def compareCMPids(mcw1: MissingCommonWrapper, mcw2: MissingCommonWrapper)
      : Int = {
    val pids1 = mcw1.commonMissingPids; val pids2 = mcw2.commonMissingPids
    // Note: pids1, pids2 are sorted by lessThan
    val len1 = pids1.length; val len2 = pids2.length
    var i1 = mcw1.pidsIndex; var i2 = mcw2.pidsIndex
    var subset1 = true; var subset2 = true
    // subset1 is true if pids1[mcw1.pidsIndex..i1) is a subset of
    // pids2[mcw2.pidsIndex..i2).  Similarly for subset2.  Only need to
    // compare from i1, i2 onwards.
    while(i1 < len1 && i2 < len2){
      if(pids1(i1) == pids2(i2)){ i1 += 1; i2 += 1 }
      else if(lessThan(pids1(i1), pids2(i2))){ subset1 = false; i1 += 1}
      else{ subset2 = false; i2 += 1 }
    }
    // Note: could bail out if !subset1 && !subset2; but the arrays are short.
    subset1 &&= i1 == len1; subset2 &&= i2 == len2
    if(subset1){ if(subset2) Equal else Subset }
    else if(subset2) Superset else Incomparable
  }

/*
  /** Keys used in keying the store map. */
  private class Key(
    val newView: ReducedComponentView, val servers: ServerStates,
    val preCpts: Array[State], val cpts: Array[State])
  {
    import StateArray.{isCanonical,mkHash1}

    require(isCanonical(preCpts) && isCanonical(cpts)) // IMPROVE

    override def hashCode = {
      val h1 = StateArray.mkHash1(newView.hashCode*71+servers.hashCode, preCpts)
      StateArray.mkHash1(h1, cpts)
    }

    override def equals(that: Any) = that match{
      case k: Key =>
        k.newView == newView && k.servers == servers &&
        k.preCpts == preCpts && k.cpts == cpts
        // Note: reference equality, because canonical
    }
  }
 */

  // private var store = 
  //   new collection.ShardedLockableMap[Key, Array[MissingCommonWrapper]]

  // def reset() = {}
  //  store = new collection.ShardedLockableMap[Key, Array[MissingCommonWrapper]]

/* This is currently disabled.  On the lock-free set example, only 23,570
 * MissingCommonWrappers are subsumed.

  /** Add mcw to store, unless it is implied by a value already there.  Return
    * true if it is added.  If mcw implies any other value in the store, then
    * mark the latter as superseded. */
  private def addToStore(mcw: MissingCommonWrapper): Boolean = {
    //println("addToStore")
    val inducedTrans = mcw.inducedTrans
    val key = new Key(inducedTrans.newView, inducedTrans.servers, 
        inducedTrans.preCpts, inducedTrans.cpts)
    store.acquireLock(key)
    store.get(key, true) match{
      case None => store.add(key, Array(mcw)); store.releaseLock(key); true

      case Some(mcws) =>
        //println("Some"+mcws.length)
        var i = 0; val len = mcws.length; var found = false
        // found is set to true if we find a MCW that implies mcw.
        // Bitmap showing those MCWs not implied by mcw, and their count
        val include = new Array[Boolean](len); var count = 0
        while(i < len && !found){
          val mcw1 = mcws(i); assert(mcw1 != mcw && !mcw1.isSuperseded)
          val cmp = compareCMPids(mcw, mcw1)
          if(cmp == Superset || cmp == Equal){
            //println(mcw.toString+"\n"+mcw1)
            found = true
          }
          if(cmp == Subset){ mcw1.setSuperseded  // mcr1 is superceded by mcr
            Profiler.count("MissingCommonWrapper.addToStore removed old") }
          else{ include(i) = true; count += 1 }
          i += 1
        } // end of while loop
        if(found && count == i){ // mcw is superseded, but none of the others is
          // No need to update store
          store.releaseLock(key); false
        }
        else{
          // None of remainder can be superseded, so include them.
          while(i < len){ include(i) = true; count += 1; i += 1 }
          // Create new array holding retained elements of oldMCRs and maybe mcr
          val newLen = if(found) count else count+1; i = 0
          val newMCWs = new Array[MissingCommonWrapper](newLen); var j = 0
          while(i < len){
            if(include(i)){ newMCWs(j) = mcws(i); j += 1 }; i += 1
          }
          assert(j == count)
          // Maybe add mcw; replace mcws with newMCWs; unlock.
          if(!found) newMCWs(count) = mcw
          store.replace(key, newMCWs, true); store.releaseLock(key)
          !found
        }
    } // end of match
  }
 */

}
