package ViewAbstraction

/** Various helper operations relating to Arrays of States. */

object StateArray{

  def show(states: Array[State]) = 
    states.map(_.toString0).mkString("[", " || ", "]")

  /** If cpt shares a process identity with cpts, are they the same state? */
  @inline
  def agreesWithCommonComponent(cpt: State, cpts: Array[State]): Boolean = {
    val cptId = cpt.componentProcessIdentity; var j = 0; var ok = true
    while(j < cpts.length && ok){
      val cpt2 = cpts(j)
      if(cpt2.componentProcessIdentity == cptId) ok = cpt == cpt2
      j += 1
    }
    ok
  }

  /** Do cpts1 and cpts2 agree on all components with the same identity?
    * Pre: cpts1(i) agrees with cpts2 on any component with the same identity. */
  def agreeOnCommonComponents(cpts1: Array[State], cpts2: Array[State], i: Int)
      : Boolean = {
    require(agreesWithCommonComponent(cpts1(i), cpts2)) // IMPROVE
    var j = 0
    while(j < cpts1.length && 
        // Use precondition to be lazy
        (j == i || agreesWithCommonComponent(cpts1(j), cpts2)) )
      j += 1
    j == cpts1.length 
  }

  /** All components referenced by principal in states, including itself. */
  def referencedStates(principal: State, states: Array[State]): Array[State] = {
    val len = principal.ids.length
    val refed = new Array[State](len); refed(0) = principal
    for(i <- 1 until len){
      val thisId = principal.ids(i)
      val matches = states.filter(_.ids(0) == thisId)
      assert(matches.length == 1)
      refed(i) = matches(0)
    }
    refed
  }



  /** The union of cpts1 and cpts2.  Pre: they agree on components with common
    * identities. */
  def union(cpts1: Array[State], cpts2: Array[State]): Array[State] = {
    val len1 = cpts1.length; val len2 = cpts2.length
    // Iterate through cpts2; count the number disjoint from cpts1, recording
    // those disjoint in newC, and check the two agree on common components.
    var i = 0; var count = 0; val newC = new Array[Boolean](len2)
    while(i < len2){
      val cpt2 = cpts2(i); val pid2 = cpt2.componentProcessIdentity; var j = 0
      // search for cpt2 in cpts1
      while(j < len1 && cpts1(j).componentProcessIdentity != pid2) j += 1
      if(j < len1) require(cpts1(j) == cpt2) else{ newC(i) = true; count += 1 }
      i += 1
    }
    // Copy cpts1 and distinct components of cpts2 (s.t. newC(_)) into result.
    val result = new Array[State](len1+count); i = 0
    while(i < len1){ result(i) = cpts1(i); i += 1}
    var j = 0
    while(j < len2){ if(newC(j)){ result(i) = cpts2(j); i += 1 }; j += 1 }
    assert(i == len1+count)
    result
  }

  /** Check components in cpts are distinct. */
  def checkDistinct(cpts: Array[State], msg: => String = "") = {
    val len = cpts.length; var i = 0
    while(i < len-1){
      var j = i+1
      while(j < len && cpts(i) != cpts(j)) j += 1
      assert(j == len, show(cpts)+" "+msg)
      i += 1
    }
  }


  /** Find the component of cpts with process identity pid, or return null if no
    * such.  IMPROVE: combine with Unification.find */
  @inline def find(pid: ProcessIdentity, cpts: Array[State]): State = {
    var i = 0
    while(i < cpts.length && cpts(i).componentProcessIdentity != pid)
      i += 1
    if(i < cpts.length) cpts(i) else null
  }

  /** Find the index of cpts with identity (f,id).  Return -1 if no such
    * index. */
  @inline def findIndex(cpts: Array[State], f: Family, id: Identity) = {
    // Search backwards to facilitate default result of -1
    var k = cpts.length-1
    while(k >= 0 && !cpts(k).hasPID(f,id)) k -= 1
    k
  }

  /** Make new Array[State] for components, with newPrinc as principal, and
    * other components from either postCpts or cpts. */
  def makePostComponents(
    newPrinc: State, postCpts: Array[State], cpts: Array[State])
      : List[Array[State]] = {
    assert(postCpts.forall(_ != null))
    assert(cpts.forall(_ != null)) // IMPROVE
    val len = newPrinc.ids.length; val pids = newPrinc.processIdentities 
    val princId = newPrinc.componentProcessIdentity
    val includeInfo = State.getIncludeInfo(newPrinc.cs)

    // Should pids(i) be included?
    @inline def include(i: Int) = {
      val pid = pids(i)
      if(!isDistinguished(pid._2) && pid != princId &&
        (includeInfo == null || includeInfo(i))){
        // check this is first occurrence of pid
        var j = 1; while(j < i && pids(j) != pid) j += 1
        j == i
      }
      else false
    }
    // find the component with identity pid in either postCpts or cpts
    @inline def findCpt(pid: ProcessIdentity): State = {
      val st1 = find(pid, postCpts)
      if(st1 != null) st1 else find(pid, cpts)
    }

    if(singleRef){
      var result = List[Array[State]](); var i = 0
      while(i < len){
        if(include(i)){
          // States corresponding to pids(i)
          val st1 = findCpt(pids(i))
          if(st1 != null) result ::= Array(newPrinc, st1)
          else println(s"No state for ${pids(i)} in ${show(postCpts)} or "+
            show(cpts))
        }
        i += 1
      }
      // if(result.length > 1) 
      //   println(s"makePostComponents: "+result.map(showStates))
      // Need to deal with the case that newPrinc has no included refs.
      if(result.nonEmpty) result else List(Array(newPrinc))
    }
    else{
      var newComponents = new Array[State](len); newComponents(0) = newPrinc
      var i = 1; var k = 1
      // Note, we might end up with fewer than len new components.
      // Inv: we have filled newComponents0[0..k) using pids[0..i).
      while(i < len){
        if(include(i)){ newComponents(k) = findCpt(pids(i)); k += 1 }
        i += 1
      }
      if(k < len){ // We avoided a repeated component; trim newComponents
        val nc = new Array[State](k); var j = 0
        while(j < k){ nc(j) = newComponents(j); j += 1 }
        newComponents = nc
      }
      if(debugging) checkDistinct(newComponents, newPrinc.toString)
      List(newComponents)
    }
  }

  /** Find all references from a component c1 of cpts1 to a component c2 of
    * cpts2 (with neither in the other), or vice versa.  Return Array(c1, c2)
    * for each such pair found. */
  def crossRefs(cpts1: Array[State], cpts2: Array[State])
      : List[Array[State]] = {
    require(singleRef) // not sure if this is necessary
    var result = List[Array[State]]()
    for(c1 <- cpts1; if !(cpts2.contains(c1))){
      val c1Params = c1.processIdentities
      for(c2 <- cpts2; if !(cpts1.contains(c2))){
        if(c1Params.contains(c2.componentProcessIdentity))
          result ::= Array(c1,c2)
        if(c2.processIdentities.contains(c1.componentProcessIdentity))
          result ::= Array(c2,c1)
      }
    }
    result
  }
}
