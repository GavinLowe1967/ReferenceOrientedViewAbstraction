package ViewAbstraction

import ox.gavin.profiling.Profiler

import ViewAbstraction.RemapperP.{Remapper,Unification}

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

// IMPROVE: use missingCandidates, as in notebook

  private var isDone = false

  /** Test whether this is now satisfied. */
  def update(views: ViewSet): Boolean = {
    isDone = MissingCommon.hasCommonRef(servers, cpts1, cpts2, pid, views)
    if(verbose && done) println(s"$this now satisfied")
    // else println(s"$this not satisfied")
    done
  }

  /** Update missingCandidates based on the addition of cv. */
  def update1(cv: ComponentView) = {
    // missingCandidates = missingCandidates.map(_.filter(_ != cv))
    // return true if any empty.
    // set found = true if we find a match
    var mcs = missingCandidates; missingCandidates = List(); var found = false
    while(mcs.nonEmpty){
      var mc = mcs.head; mcs = mcs.tail; var newMc = List[ComponentView]()
      while(mc.nonEmpty){
        val cv1 = mc.head; mc = mc.tail
        if(cv1 != cv) newMc ::= cv1 else found = true
      }
      if(newMc.isEmpty) println(s"update1: $this")
      else missingCandidates ::= newMc
    }
    assert(found)
  }

  @inline def done = isDone

  /** Is cv a possible match to clause (1), i.e. does it match servers ||
    * cpts1(0) || c? */
  def matches(cv: ComponentView) = 
    cv.servers == servers && cv.components(0) == princ1
  // IMPROVE: can we also ensure that cv.components(1).processIdentity == pid?

  /** Update this based on using cv to instantiate servers || princ1 || c. */
  def updateMC(cv: ComponentView, views: ViewSet): Boolean = {
    require(matches(cv))
    val cpt1 = cv.components(1)
    if(cpt1.hasPID(pid)){
      val oldMissingCandidates = missingCandidates
      if(MissingCommon.updateMissingCandidates(this, cpt1, views)){
        // println(s"updateMC($cv):\n  $this\nCompleted!")
        isDone = true
      }
      if(missingCandidates != oldMissingCandidates){
        // Should have added at the front
        val lenDiff = missingCandidates.length - oldMissingCandidates.length
        assert(missingCandidates.drop(lenDiff) == oldMissingCandidates)
        // println("Added: "+missingCandidates.take(lenDiff))
        // println(s"missingCandidates = $missingCandidates;\n"+
        //   s"oldMissingcandidates == $oldMissingCandidates")
      }
    }
    isDone
  }

  def allCandidates: List[ComponentView] = missingCandidates.flatten.distinct

  override def toString = 
    s"MissingCommon($servers, ${StateArray.show(cpts1)},"+
      s"  ${StateArray.show(cpts2)}, $pid)"
}


// =======================================================

object MissingCommon{
  /** Is there a component state c with identity pid such that sysAbsViews
    * contains each of the following (up to renaming): (1) servers || princ1
    * || c; (2) servers || princ2 || c; (3) if c has a reference to a
    * component c2 of cpts2 then servers || c || c2? */
// IMPROVE comments
  @inline def hasCommonRef(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State], 
    pid: ProcessIdentity, views: ViewSet)
      : Boolean = {
    assert(singleRef)
    assert(cpts1.length == 2, StateArray.show(cpts1))
    assert(cpts2.length == 2, StateArray.show(cpts2))
    val princ1 = cpts1(0); val princ2 = cpts2(0); var found = false
    // All elements of views of the form servers || princ1 || c where c has
    // identity pid
    var matches = matchesFor(servers, princ1, pid, views)
    while(matches.nonEmpty && !found){
      val cv1 = matches.head; matches = matches.tail
      val cpt1 = cv1.components(1); assert(cpt1.hasPID(pid))
      // All relevant renamings of cpt1: identity on params of servers and
      // princ1, but otherwise either to other params of cpts2 or to fresh
      // values.
// FIXME: also rename to other params of cpts1?
      val renames = Unification.remapToJoin(servers, princ1, cpts2, cpt1)
      var i = 0
      while(i < renames.length && !found){
        val c = renames(i); i += 1
        val cvx = Remapper.mkComponentView(servers, Array(princ2, c))
        if(views.contains(cvx)){
          found = true; var j = 1
          // Test if there is a view with c as principal, with a reference
          // to a secondary component of cpts1 or cpts2
          while(j < c.length){ // && found ?
            val pid2 = c.processIdentities(j); j += 1
            val c2 = StateArray.find(pid2, cpts2)
// FIXME: also cpts1?
            if(c2 != null){
              val cvx2 = Remapper.mkComponentView(servers, Array(c, c2))
              if(views.contains(cvx2)){ } //  println(s"Contains $cvx2")
              else{
                found = false
                if(false) println(
                  s"hasCommonRef($servers, ${StateArray.show(cpts1)}, "+
                    s"${StateArray.show(cpts2)}): ${c.toString0} -> "+
                    c2.toString0+s"\nNot contains $cvx2")
              }
            }
          }
        }
      } // end of inner while
    } // end of outer while
    found
  }

  /** A MissingCommon object, corresponding to servers, cpts1, cpts2 and pid, or
    * null if the obligation is already satisfied.
    * 
    * For each component state c such that servers || cpts1(0) || c is in
    * views, missingCandidates contains the list of Views that are needed to
    * satisfy the obligation but are currently missing from views: (1) servers
    * || cpts2(0) || c; and (2) if c has a reference to a secondary component
    * c2 of cpts1 or cpts2, then servers || c || c2 (renamed).
    */
  def makeMissingCommon(
    servers: ServerStates, cpts1: Array[State], cpts2: Array[State], 
    pid: ProcessIdentity, views: ViewSet)
      : MissingCommon = {
    Profiler.count("makeMissingCommon")
    assert(singleRef)
    assert(cpts1.length == 2, StateArray.show(cpts1))
    assert(cpts2.length == 2, StateArray.show(cpts2))
    val princ1 = cpts1(0); val princ2 = cpts2(0); var found = false
    val mc = new MissingCommon(servers, cpts1, cpts2, pid)
    // All elements of views of the form servers || princ1 || c where c has
    // identity pid
    var matches = matchesFor(servers, princ1, pid, views)
    while(matches.nonEmpty && !found){
      val cv1 = matches.head; matches = matches.tail
      found = updateMissingCandidates(mc, cv1.components(1), views)
    } // end of while loop
    if(found) null 
    else{ Profiler.count("MissingCandidateSize"+mc.allCandidates.length); mc }
  }

  /** Update mc.missingCandidates to include lists of missing views
    * corresponding to instantiating c with a renaming of cpt1.
    * @return true if mc is now complete. */
  @inline private 
  def updateMissingCandidates(mc: MissingCommon, cpt1: State, views: ViewSet)
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
      val missing = getMissingCandidates(mc.servers, mc.cpts2, c, views)
      if(missing.isEmpty) found = true
      else mc.missingCandidates ::= missing
    } // end of while loop
    found
  }

  /** Find the missing Views that are necessary to complete a MissingCommon for
    * a particular candidate state c.  Return a list containing each of the
    * following that is not currently in views: (1) servers || cpts2(0) || c;
    * and (2) if c has a reference to a secondary component c2 of cpts1 or
    * cpts2, then servers || c || c2 (renamed). */
// IMPROVE: not currently cpts1
  @inline private def getMissingCandidates(
    servers: ServerStates, cpts2: Array[State], c: State, views: ViewSet)
  : List[ComponentView] = {
    var missing = List[ComponentView]() // missing necessary views
    val cvx = Remapper.mkComponentView(servers, Array(cpts2(0), c))
    if(!views.contains(cvx)) missing ::= cvx
    // If c has a reference to a secondary component c2 of cpts2 or FIXME
    // cpts1, then the View servers || c || c2 is necessary.
    var j = 1
    while(j < c.length){
      val pid2 = c.processIdentities(j); j += 1
      val c2 = StateArray.find(pid2, cpts2)
// FIXME: also cpts1?
      if(c2 != null){
        val cvx2 = Remapper.mkComponentView(servers, Array(c, c2))
        if(!views.contains(cvx2)) missing ::= cvx2
      }
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
