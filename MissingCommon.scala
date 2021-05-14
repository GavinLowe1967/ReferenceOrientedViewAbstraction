package ViewAbstraction

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
  require(cpts1(0).processIdentities.contains(pid) && 
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

  @inline def done = isDone

  override def toString = 
    s"MissingCommon($servers, ${StateArray.show(cpts1)},\n"+
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
    val princ1 = cpts1(0); val princ2 = cpts2(0)
    val iter = views.iterator(servers, princ1); var found = false
    // All elements of views of the form servers || princ1 || c where c has
    // identity pid
    var matches = matchesFor(servers, princ1, pid, views)
    while(matches.nonEmpty && !found){
      val cv1 = matches.head; matches = matches.tail
      val cpt1 = cv1.components(1)
    // while(iter.hasNext && !found){
    //   val cv1 = iter.next; val cptsX = cv1.components
    //   assert(cptsX.length == 2, cv1); val cpt1 = cptsX(1)
    //   if(cpt1.hasPID(pid)){

    // All relevant renamings of cpt1: identity on params of servers and
    // princ1, but otherwise either to other params of cpts2 or to fresh
    // values.
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

  /** All elements of views of the form servers || princ || c where c has
    * identity pid. */
  @inline private def matchesFor(
    servers: ServerStates, princ: State, pid: ProcessIdentity, views: ViewSet)
      : List[ComponentView] = {
    var result = List[ComponentView]()
    val iter = views.iterator(servers, princ); var found = false
    while(iter.hasNext){
      val cv = iter.next; val cpts = cv.components; assert(cpts.length == 2, cv)
      if(cpts(1).hasPID(pid)) result ::= cv
    }
    result
  }


}
