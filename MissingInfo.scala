package ViewAbstraction
import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet}

/** Information capturing when newView might be added to the ViewSet: once all
  * of missingViews have been added, and all the obligations represented by
  * missingCommon have been satisfied. 
  * 
  * This corresponds to transition trans inducing
  * cv == (pre.servers, oldCpts) -> (post.servers, newCpts) == newView. */
// IMPROVE: can we store these in a more memory-efficient way?  Do we need
// them all?  
class MissingInfo(
  val newView: ReducedComponentView, 
  var missingViews: Array[ReducedComponentView], 
  var missingCommon: Array[MissingCommon], trans: Transition,
  val oldCpts: Array[State], val cv: ComponentView, val newCpts: Array[State]
){
  /* missingViews contains component views that are necessary to satisfy this
   * constraint: all must be added to the ViewSet.  This corresponds to
   * condition (b) in the definition of induced transitions with restricted
   * views.
   * 
   * missingCommon stores information about views necessary to satisfy this
   * constraint.  Each represents an obligation to instantiate a component
   * with a particular identity.  This corresponds to condition (c) in the
   * definition of induced transitions with restricted views.  All must be
   * satisfied in order to satisfy this constraint.
   * 
   * Note: MissingCommon values might be shared between MissingInfo objects.
   * 
   * Each is replaced by null when satisfied.  It will be unusual for
   * missingViews to contain more than about four elements, or for
   * missingCommon to contain more than one element.  So we don't compact the
   * arrays.  */

  /* Overview of main functions.
   * updateMissingCommon     (called from EffectOnStore.comlpeteCandidateForMC)
   * |--(MissingCommon.)updateWithNewMatch
   * |--advanceMC
   *    |--(MissingCommon.)updateMissingViews
   *    |--updateMissingViews
   * 
   * updateMissingViewsOfMissingCommon    (called from EffectOnStore)
   * |--(MissingCommon.)updateMissingViewsBy
   * |--advanceMC
   * 
   * updateMissingViewsBy    (called from EffectOnStore)
   * |--updateMissingViews
   * 
   * done, mcDone, missingHead, markNewViewFound, missingViewsUpdated, 
   * setNotAdded, sanity1, sanityCheck, equals, hashCode, size
   */

  def pre = trans.pre
  def post = trans.post
  def e = trans.e

  /** For debugging. oldCpts = [31(T1,N3,N2,N1) || 10(N3,Null,N2)] */
  @inline private def highlight = false &&
    ComponentView0.highlight(newView) && Transition.highlight(trans) && {
      val princ = oldCpts(0)
      princ.cs == 31 && {
        val second = oldCpts(1)
        second.cs == 10 && second.ids.sameElements(Array(3,-1,2))
      }
    }

  if(highlight) println(s"Created $this")

  require(missingCommon.forall(!_.done))
  require(missingViews.forall(_ != null))

  // We keep missingCommon and missingViews sorted. 
  MissingInfo.sort(missingCommon, missingViews)

  /* missingViews may contain null values: duplicates are replaced by null in
   * the above sort. */

  import MissingCommon.CptsBuffer // ArrayBuffer[ComponentView]

  assert(missingCommon.length <= 2, 
    "missingCommon.length = "+missingCommon.length)
  assert(missingViews.length <= 9, "missingViews.length = "+missingViews.length)
  // FIXME: latter not true in general.  I don't think the former is, either

  /* Initially we try to discharge the obligations represented by missingCommon.
   * mcIndex represents the next MissingCommon to consider; mcDone gives true
   * when all are satisfied.  Subsequently, the obligations represented by
   * missingViews are considered.   */

  // Remove empty array, to reduce memory usage.
  if(missingCommon.isEmpty) missingCommon = null

  /** Index of the first non-null entry in missingCommon, or
    * missingCommon.length if all are null.  Invariant:
    * missingCommon[0..mcIndex).forall(_ == null). */
  private var mcIndex = 0

  import MissingInfo.LogEntry

  /** Log used for debugging, stored in reverse. */
  // var theLog = List[LogEntry]()

  /** Log for debugging purposes.  Currently turned off. */
  def log(item: LogEntry) = {} 
  // def log(item: LogEntry) = synchronized{ theLog ::= item }

  // def showLog = theLog.reverse.mkString("\n")

  /** Record missingCommon(i) as being completed. */
  @inline private def mcNull(i: Int) = {
    require(missingCommon(i).done); missingCommon(i) = null 
  }

  @inline private def logAdvanceMC = 
    log(MissingInfo.AdvanceMC(missingCommon.length-mcIndex))

  /** Advance to the next MissingCommon value (if any).  Otherwise, update the 
    * missingViews.
    * @return a CptsBuffer containing views against which this should now be 
    * registered, or null if all MissingCommon are done. */
  @inline private 
  def advanceMC(views: ViewSet): CptsBuffer = {
    if(highlight) println("advanceMC")
    // Deal with case that all MissingCommon are done.  Null out missingCommon
    // to reduce memory usage.  We also update missingViews in case a prefix
    // of them is done.
    @inline def allMCDone() = { 
      missingCommon = null; rehashMC(); updateMissingViews(views); null 
    }

    require(missingCommon(mcIndex) == null)
    mcIndex += 1;  logAdvanceMC
    if(mcIndex < missingCommon.length){ // consider next 
      assert(mcIndex == 1 && missingCommon.length == 2)
      val mc = missingCommon(mcIndex)
      if(mc == null){ // this one is also done
        mcIndex += 1; logAdvanceMC; allMCDone(); 
      } 
      else{
        val vb = mc.updateMissingViews(views)
        if(vb == null){  // and now this is done
          assert(mc.done); mcNull(mcIndex); mcIndex += 1; allMCDone(); 
        }
        else{ rehashMC(); vb }
      }
    }
    else allMCDone() 
  }

  /** Are all the missingCommon entries done? */
  @inline def mcDone = synchronized{ 
    missingCommon == null || mcIndex == missingCommon.length 
  }

  /** Are all the missingCommon entries done?  Also performs a sanity check,
    * that mcIndex doesn't point to a done MissingCommon. */
  @inline def getMcDone/*(key: String)*/ = synchronized{ 
    if(missingCommon == null || mcIndex == missingCommon.length) true
    else{
// Note, I think the following might fail when notAdded is true
      assert(!missingCommon(mcIndex).done, s"$this") // \nkey = $key
      false
    }
  }

  /** Index of first non-null missingView.  Once all MissingCommon are complete,
    * this will be registered against missingViews(mvIndex) in
    * EffectOnStore.store.  */
  private var mvIndex = 0

  /** The first missing view, against which this should be registered once all
    * the MissingCommon are done. */
  def missingHead = synchronized{ missingViews(mvIndex) }

  /** Has newView been found already? */
  private var newViewFound = false

  /** Record that newView has already been seen, so this is redundant. */
  def markNewViewFound = synchronized{
    // log(MissingInfo.MarkNewViewFound)
    // if(highlight) println(s"markNewViewFound:\n$this")
    newViewFound = true
  }

  /** Does views contain newView?  Store the result. */
  def isNewViewFound(views: ViewSet) = synchronized{
    if(views.contains(newView)){ newViewFound = true; true } else false
  }

  /** Is this complete? */
  @inline def done = 
    synchronized{ mcDone && mvIndex == missingViews.length || newViewFound }

  /** Has this been put into the mcDoneStore? */
  @volatile var transferred = false

  /** Update the MissingCommon entries in this, based on cv being a possible
    * match to the first clause of the obligation.  cv is expected to be a
    * possible match to the next element of missingCommon.  If all
    * missingCommon are done, also update missingViews.
    * @return a CptsBuffer containing all views that this needs to be registered
    * against in the store if not all MissingCommon are done. */
  def updateMissingCommon(cv: ComponentView, views: ViewSet)
    // , key: (ServerStates,State) // the key is only for logging
      : CptsBuffer = synchronized{
    // log(MissingInfo.UpdateWithNewMatch(cv,key))
    if(highlight) println(s"\nupdateMissingCommon($cv)")
    assert(!mcDone)
    if(mcIndex == missingCommon.length-1){ 
      // Note: this has the same effect as the else clause, but is simpler.
      val mc = missingCommon(mcIndex); assert(mc != null && mc.matches(cv))
      // mc.log(MissingCommon.UpdateWithNewMatch(cv, key))
      val vb = mc.updateWithNewMatch(cv, views)
      if(vb == null){
        // Advance to the next MissingCommon (if any), and return views to
        // register against
        assert(mc.done); mcNull(mcIndex); advanceMC(views)
      }
      else vb
    }
    else{
      var vb: CptsBuffer = null // holds result
      /* Add vb1 to vb. */
      @inline def addTovb(vb1: CptsBuffer) = 
        if(vb == null) vb = vb1 else vb ++= vb1
      /* Deal with a missingCommon that is either null or done. */
      @inline def dealWithDone(index: Int) = {
        if(index == mcIndex){
          // Advance to the next MissingCommon (if any), and store views to
          // register against
          val vb2 = advanceMC(views); if(vb2 != null) addTovb(vb2)
        }
        else rehashMC()
      }
      assert(missingCommon != null)
      var index = mcIndex
      // Note: missingCommon might be set to null by an iteration
      while(missingCommon != null && index < missingCommon.length){
        // for(index <- mcIndex until missingCommon.length){
        val mc = missingCommon(index) 
        if(mc != null){
          assert(mc.matches(cv), s"mc = $mc; cv = $cv")
          val vb1 = mc.updateWithNewMatch(cv, views)
          if(vb1 == null){ assert(mc.done); mcNull(index); dealWithDone(index) }
          else addTovb(vb1)
        } // end of if mc != null
        else dealWithDone(index)
        index += 1
      } // end of while
      vb
    }
  }

  /** Update the missing views in the MissingCommon fields of this.
    * @return the views against which this should now be registered, or
    * null if all the missingCommon entries are satisfied.  If all
    * missingCommon are done, also update missingViews. */ 
  def updateMissingViewsOfMissingCommon(views: ViewSet)
      : CptsBuffer = synchronized{
    if(highlight) println("updateMissingViewsOfMissingCommon")
    val mc = missingCommon(mcIndex)
    val vb: CptsBuffer = mc.updateMissingViews(views)
    if(vb == null){ assert(mc.done); mcNull(mcIndex); advanceMC(views) }
    else vb
  }

  /** Update missingViews and mvIndex based upon views.  This is called either
    * when all MissingCommon are first complete (from advanceMC), or from
    * updateMissingViewsBy, to advance over subsequent missing views in
    * views.  */
  private def updateMissingViews(views: ViewSet) = {
    require(mcDone)
    // Profiler.count("updateMissingViews "+
    //   (mvIndex < missingViews.length &&
    //   (missingViews(mvIndex) == null || views.contains(missingViews(mvIndex)))))
    while(mvIndex < missingViews.length && 
      (missingViews(mvIndex) == null || views.contains(missingViews(mvIndex)))){
      missingViews(mvIndex) = null; mvIndex += 1
    }
    rehashMV()
  }

  /** Check that missingViews is up-to-date with views.  Used in assertions. */
  def missingViewsUpdated(views: ViewSet): Boolean = synchronized{
    mvIndex == missingViews.length || !views.contains(missingViews(mvIndex))
  }

  /** Update missingViews and mvIndex based on the addition of cv.  cv is
    * expected to match the next missing view. */
  def updateMissingViewsBy(cv: ComponentView, views: ViewSet) = synchronized{
    // Note: the assertion below is checked in EffectOnStore, within a
    // synchronized block on this, so the following is not a TOCTTOU.
    require(mcDone && mvIndex < missingViews.length && 
      missingViews(mvIndex) == cv,
      s"mvIndex = $mvIndex, cv = $cv, missingViews = \n"+
        missingViews.mkString("\n"))
//    val oldMissingViews = missingViews.clone
    missingViews(mvIndex) = null; mvIndex += 1
    updateMissingViews(views)
// Replace in MissingInfoStore
  }

  private var notAdded = false

  /** Record that an attempt to add this to a Store in EffectOnStore failed,
    * because an equivalent MissingInfo was already there.  This means that
    * the expected invariant might not hold: missingCommon values in this may
    * still retain a view that is in the current view set.  This affects the
    * check in sanityCheck below. */
  def setNotAdded = synchronized{ notAdded = true }

  /** Check that we have nulled-out all done MissingCommons. */
  def sanity1 = 
    missingCommon == null || missingCommon.forall(mc => mc == null || !mc.done)

  /** Check that: (1) if all the MissingCommon objects are done, then views does
    * not contain missingHead; (2) otherwise the first non-done MissingCommon
    * object has a head missingView in views; (3) if flag, then all
    * MissingCommon objects are done (but not necessarily vice versa).
    * However, if flag is false and notAdded is true, this was might have been
    * replaced by a different but equivalence object in the relevant place, so
    * not be up to date with respect to (1). */
  def sanityCheck(views: ViewSet, flag: Boolean) = {
    assert(!done)
    if(flag) assert(mcDone) // Check (3)
    if(mcDone){
      if(!flag) assert(transferred)
      assert(missingCommon == null)
      if(flag || !notAdded) //  IMPROVE: do we need this guard? 
        assert(!views.contains(missingHead),  // Check (1)
          s"$this\nstill contains $missingHead.\n") // + showLog
      else Profiler.count("missingInfo sanity check skipped")
    }
    else{ 
      // Check the first non-done missingCommon is up to date
      var done = false // have we seen a non-done missingCommon?
      for(mc <- missingCommon){
        if(!done && mc != null){ 
          mc.sanityCheck(views) // check (2)
          if(!mc.done) done = true // no need to check further
        }
      }
    }
  }

  override def toString =
    s"MissingInfo(newView = $newView,\n  cv = $cv,\n  oldCpts = "+
      StateArray.show(oldCpts)+
      s"\n  missingViews = ${missingViews.mkString("<",",",">")},\n"+
      "  missingCommon = "+
      (if(missingCommon == null) "null\n" 
      else missingCommon.mkString("<",",\n  ",">")+")\n")+
      s"  notAdded = $notAdded; mcDone = $mcDone; mcIndex = $mcIndex; "+
      s"done = $done\n" // + showLog

  /* Note: we override equality and hashCode, since these leads to fewer
   * MissingInfos being stored, at least in McDoneSet.  This needs more
   * experimentation. */

  /** Equality: same newView, missingViews and missingCommon (up to equality,
    * ignoring nulls). */
// FIXME: is locking of that useful/necessary here?  I think this is used only
// when building sets of MissingInfos.  
  override def equals(that: Any) = synchronized{ 
    that match{
      case mi: MissingInfo =>
        mi.newView == newView &&
        MissingInfo.equalExceptNull(mi.missingViews, missingViews) &&
        // same missingCommon, maybe both null
        (if(mi.missingCommon == null) missingCommon == null
        else missingCommon != null &&
          MissingInfo.equalExceptNull(mi.missingCommon, missingCommon))
    }
  }

  /** The hash code for this. */
  override def hashCode = synchronized{ mcHash ^ mvHash }

  /** Hash of newView and missingCommon. */
  private var mcHash = -1

  /** Update mcHash.  Should be called at each update of mcIndex. */
  @inline private def rehashMC() = 
    mcHash = MissingInfo.hashMC(newView, missingCommon, mcIndex)
  //   var h = newView.hashCode
  //   if(missingCommon != null){
  //     var i = mcIndex
  //     while(i < missingCommon.length){
  //       if(missingCommon(i) != null) h = h*73 + missingCommon(i).hashCode
  //       i += 1
  //     }
  //   }
  //   mcHash = h
  // }

  /** Hash of missingViews. */
  private var mvHash = -1

  /** Update mvHash.  Should be called at each update of mvIndex. */
  private def rehashMV() = mvHash = MissingInfo.hashMV(missingViews, mvIndex)
  //   var h = 0; var i = mvIndex
  //   while(i < missingViews.length){
  //     if(missingViews(i) != null) h = h*73 + missingViews(i).hashCode
  //     i += 1
  //   }
  //   mvHash = h
  // }

  rehashMC(); rehashMV()

  /** Estimate of the size of this. 
    * @return a pair: the number of views in missingViews; and the number of 
    * views in missingCommon. */
  def size: (Int, Int) = {
    var viewCount = 0; var ix = 0
    while(ix < missingViews.length){ 
      if(missingViews(ix) != null) viewCount += 1
      ix += 1
    }
    var mcCount = 0
    if(missingCommon != null){
      if(missingCommon.length == 1){ // optimise for this case
        if(missingCommon(0) != null) mcCount = missingCommon(0).size
      }
      else{
        var i = 0
        while(i < missingCommon.length){
          if(missingCommon(i) != null) mcCount += missingCommon(i).size
          i += 1
        }
      }
    }
    (viewCount, mcCount)
  }

}

// ==================================================================

/** Companion object. */
object MissingInfo{
  /** A hash of newView and the non-null entries in missingCommon[start..). */
  @inline def hashMC(newView: ReducedComponentView,
    missingCommon: Array[MissingCommon], start: Int)
      : Int = {
    var h = newView.hashCode
    if(missingCommon != null){
      var i = start
      while(i < missingCommon.length){
        if(missingCommon(i) != null) h = h*73 + missingCommon(i).hashCode
        i += 1
      }
    }
    h
  }

  @inline def hashMV(missingViews: Array[ReducedComponentView], start: Int)
      : Int = {
    var h = 0; var i = start
    while(i < missingViews.length){
      if(missingViews(i) != null) h = h*73 + missingViews(i).hashCode
      i += 1
    }
    h
  }


  /** Sort missingCommon and missingViews. */
  private def sort(missingCommon: Array[MissingCommon], 
    missingViews: Array[ReducedComponentView])
  = {
    require(missingCommon.length <= 2)
    // Sort missingCommon
    if(missingCommon.length == 2){
      val cmp = missingCommon(0).compare(missingCommon(1))
      if(cmp > 0){
        val t = missingCommon(0); missingCommon(0) = missingCommon(1);
        missingCommon(1) = t
      }
      else if(cmp == 0) // happens on step 46 of lazySet.csp, after ~100K views
        missingCommon(1) = null
    }
    // Sort missingViews.  Also replace duplicates by null.  Use insertion
    // sort, as the array is small.
    var i = 1 // Inv: sorted missingViews[0..i)
    while(i < missingViews.length){
      val mv = missingViews(i); var j = i; i += 1
      // Inv missingViews[j+1..i) > mv; missingViews(j) is a duplicate or
      // equals mv, so missingViews[0..j)++missingViews[j+1..i)++[mv] is a
      // permutation of missingViews[0..i) at the start of this iteration.
      while(j > 0 && 
          (missingViews(j-1) == null || mv.compare(missingViews(j-1)) < 0)){
        missingViews(j) = missingViews(j-1); j -= 1
      }
      // Copy mv into position, unless duplicted by missingViews(j-1)
      if(j == 0 || missingViews(j-1) != mv) missingViews(j) = mv
      else missingViews(j) = null // ; remainingCount -= 1 
    }
  }

  /** Do xs and ys hold the same non-null values? */
  @inline  def equalExceptNull[A](xs: Array[A], ys: Array[A]) = {
    var i = 0; var j = 0
    while(i < xs.length && xs(i) == null) i += 1
    while(j < ys.length && ys(j) == null) j += 1
    // Inv: xs[0..i) and ys[0..j) contain same non-null values, and i, j are
    // at end of array or point to non-null values.
    while(i < xs.length && j < ys.length && xs(i) == ys(j)){
      i += 1; j += 1
      while(i < xs.length && xs(i) == null) i += 1
      while(j < ys.length && ys(j) == null) j += 1
    }
    i == xs.length && j == ys.length 
  }

  // Entries in the log of a MissingInfo.  Used for debugging
  trait LogEntry
  // case class McDoneStore(cv: ReducedComponentView) extends LogEntry

  /** This is stored in the mcNotDoneStore against cv. */
  case class McNotDoneStore(cv: ReducedComponentView, ply: Int) extends LogEntry

  /** This is added to candidateForMCStore against (servers,princ). */
  case class CandidateForMC(servers: ServerStates, princ: State, ply: Int)
      extends LogEntry

  // case object MarkNewViewFound extends LogEntry
  /** A call to advanceMC that leaves `remaining` MissingCommons. */
  case class AdvanceMC(remaining: Int) extends LogEntry
  // case class NotStored(st: String) extends LogEntry

  /** A call to updateWithNewMatch(cv) corresponding to key. */
  case class UpdateWithNewMatch(
    cv: ComponentView, key: (ServerStates, State)) 
      extends LogEntry

  /** An iteration of EffectOnStore.completeCandidateForMC saw this. */
  case class CCFMCIter(cv: ComponentView) extends LogEntry

  /** An iteration of completeMcNotDone(cv) saw this. */
  case class CMNDIter(cv: ComponentView, ply: Int) extends LogEntry
}

// ==================================================================

import scala.collection.mutable.HashMap

/** A store of all the current MissingInfos. */
object MissingInfoStore{
  /** Keys used in the mapping. */
  private class Key(val newView: ReducedComponentView,
      val missingViews: Array[ReducedComponentView],
      val missingCommon: Array[MissingCommon]){

    /** Equality is equality of non-null elements.  Note: each parameter is
      * expected to be sorted. */
    override def equals(that: Any) = that match{
      case k: Key =>
        k.newView == newView && 
        MissingInfo.equalExceptNull(k.missingViews, missingViews) && 
        (if(missingCommon == null) k.missingCommon == null
        else k.missingCommon != null &&
          MissingInfo.equalExceptNull(k.missingCommon, missingCommon) )
    }

    override def hashCode = 
      MissingInfo.hashMC(newView, missingCommon, 0) ^ 
      MissingInfo.hashMV(missingViews, 0)
  } // end of Key

  /** The number of shards used in the store. */
  private val numShards = powerOfTwoAtLeast(numWorkers) * 32

// IMPROVE: make the contains operation lock-free

// IMPROVE: we don't do anything with the stored MissingInfos!  But could
// purge when the MissingInfo is done.

  /** The underlying store. */
  private var store = new ShardedHashMap[Key, MissingInfo](shards = numShards)

  /* Note: if two MissingInfos have the same newView, and the constraints of one
   * are a subset of those of another, then we aim not to include the latter.
   * We don't do this completely, as we don't purge supersets when we add a
   * new value.  Also, concurrent adds might not see the effect of the other.
   * However, this doesn't matter, as this is only a heuristic. */

  /** Does the store contain a MissingInfo for newView and a subset of
    * missingViews and missingCommon? */
  private def containsSubset(newView: ReducedComponentView,
    missingViews: Array[ReducedComponentView], 
    missingCommon: Array[MissingCommon])
  : Boolean = {
    assert(missingViews != null)
    // Consider each subset of missingViews. 
    // Each subset is represented by a value for flags.  We only set entries
    // in flags corresponding to non-null entries in missingViews.
    // Considering flags as a number in binary, we consider each value in
    // turn.  found is true if we've found a subset.  Inv: we've considered
    // each subset up to and including flags.  done is true if we've
    // considered them all or found a subset.
// FIXME: and MissingCommon
    val flags = new Array[Boolean](missingViews.length)
    var done = false; var found = false
    while(!done){
      // Advance flags to next subset.  In effect, we increment the number
      // represented by flags (in binary), but skipping over bits that
      // correspond to nulls in missingViews.
      var done1 = false; var i = 0
      /* Advance i to next non-null element of missingViews. */
      @inline def advance() =
        while(i < missingViews.length && missingViews(i) == null) i += 1
      advance()
      while(i < missingViews.length && !done1){
        assert(missingViews(i) != null); flags(i) = !flags(i)
        if(flags(i)) done1 = true else{ i += 1; advance() }
      }
      if(done1){
        // The subset of missingViews corresponding to flags.
        val missingViews1 = Array.tabulate(missingViews.length)(i =>
          if(flags(i)) missingViews(i) else null)
        val key = new Key(newView, missingViews1, missingCommon)
        if(store.contains(key)){ found = true; done = true }
      }
      else done = true
    }
    found
  }


  /** Add mi if there is no existing MissingInfo that represents a subset of the
    * constraints. */
  @inline def add(mi: MissingInfo): Boolean = {
    val newView = mi.newView
    val missingViews = mi.missingViews; val missingCommon = mi.missingCommon
    if(!containsSubset(newView, missingViews, missingCommon)){
      val key = new Key(newView, missingViews, missingCommon)
      store += key -> mi 
      true
    }
    else{ mi.setNotAdded; false }
  }
// IMPROVE: better to construct the missingInfo here when first adding.

  /** Remove the entry corresponding to mi but using oldMissingViews; replace it
    * with mi if there is no subset. */
  def replace(mi: MissingInfo, oldMissingViews: Array[ReducedComponentView])
      : Boolean = {
    // Note: we try to make the remove and add as close together as possible. 
    val newView = mi.newView; val newMissingViews = mi.missingViews
    val missingCommon = mi.missingCommon
    val oldKey = new Key(newView, oldMissingViews, missingCommon)
    if(!containsSubset(newView, newMissingViews, missingCommon)){
      val newKey =  new Key(newView, newMissingViews, missingCommon)
      store.remove(oldKey); store += newKey -> mi; true
    }
    else{ store.remove(oldKey); false }
  }

  /** Remove mi from the store. */
  def remove(mi: MissingInfo) = {
    val key = new Key(mi.newView, mi.missingViews, mi.missingCommon)
    store.remove(key)
  }

  /** Reset for a new check. */
  def reset = store = new ShardedHashMap[Key, MissingInfo](shards = numShards)

}
