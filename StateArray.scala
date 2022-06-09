package ViewAbstraction

/** Various helper operations relating to Arrays of States. */

object StateArray{
  /** Convert states into a String. */
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
    while(i < cpts.length && !cpts(i).hasPID(pid))
      i += 1
    if(i < cpts.length) cpts(i) else null
  }

  /** Find the component of cpts with process identity (f,id), or return null if
    * no such.  */
  @inline def find(cpts: Array[State], f: Family, id: Identity): State = {
    var i = 0
    while(i < cpts.length && !cpts(i).hasPID(f, id)) i += 1
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
    * other components from either postCpts or cpts.  In the case of
    * singleRef, we require that the secondary component is not a missing
    * component in cpts. */
  def makePostComponents(
    newPrinc: State, postCpts: Array[State], cpts: Array[State])
      : List[Array[State]] = {
    assert(postCpts.forall(_ != null))
    assert(cpts.forall(_ != null)) // IMPROVE
    val len = newPrinc.ids.length; val pids = newPrinc.processIdentities 
    val princId = newPrinc.componentProcessIdentity
    //val includeInfo = State.getIncludeInfo(newPrinc.cs)

    // Should pids(i) be included?
    @inline def include(i: Int) = {
      val pid = pids(i) ; val (f,id) = pid
      if(!isDistinguished(pid._2) && pid != princId && newPrinc.includeParam(i)){
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
      var result = List[Array[State]](); var i = 0; var otherRef = false
      // otherRef is set to true if there is a reference from pids that is a
      // missing reference from cpts, or is to a component not present in cpts
      // or postCpts.  Otherwise, we return the singleton Array(newPrinc),
      // since that is the only relevant view.
      while(i < len){
        if(include(i)){
          // Check this isn't a missing component
          val (f,id) = pids(i)
          if(cpts(0).hasIncludedParam(f,id) && find(cpts, f, id) == null)
            otherRef = true
          else{
            // States corresponding to pids(i)
            val st1 = findCpt(pids(i))
            if(st1 != null) result ::= Array(newPrinc, st1)
            else otherRef = true
          }
        }
        i += 1
      }
      if(result.nonEmpty || otherRef) result 
      else{ 
        // If we've got here, all the non-identity parameters of newPrinc must
        // be distinguished or omitted.
        for(i <- 1 until len)
          assert(isDistinguished(pids(i)._2) || pids(i) == princId ||
            !newPrinc.includeParam(i),
            s"newPrinc = $newPrinc; postCpts = ${show(postCpts)}\n"+
              s"cpts = ${show(cpts)}")
        List(Array(newPrinc))
      }
      // If all the refs from newPrinc are distinguished, we need
      // to include the singleton view.
    } // end of singleRef case
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

  /** Does cpts contain cpt? */
  @inline private def contains(cpts: Array[State], cpt: State): Boolean = {
    var i = 0
    while(i < cpts.length && cpts(i) != cpt) i += 1
    i < cpts.length
  }

  /** Flag used in the definition of crossRefs. */
  val CrossRefFlag = true
  // Setting this false roughly doubles the number of views for lazySetNoDel.

  /** Find all references from a component c1 of cpts1 to a component c2 of
    * cpts2 (with neither in the other), or vice versa.  Return Array(c1, c2)
    * for each such pair found (where c1 has a reference to c2).  If
    * crossRefFlag is false, include the cross reference only if a principal
    * also has a reference to one of the components. */
  def crossRefs(cpts1: Array[State], cpts2: Array[State])
      : List[Array[State]] = {
    require(singleRef)
    if(CrossRefFlag){
      var result = List[Array[State]](); var i = 0
      while(i < cpts1.length){
        val c1 = cpts1(i); i += 1
        if(! contains(cpts2, c1)){
          var j = 0
          while(j < cpts2.length){
            val c2 = cpts2(j); j += 1
            if(! contains(cpts1, c2)){
              // Cross reference from cpts1 to cpts2
              if(c1.hasIncludedParam(c2.family, c2.id)) result ::= Array(c1,c2)
              // Cross reference from cpts2 to cpts1
              if(c2.hasIncludedParam(c1.family, c1.id)) result ::= Array(c2,c1)
            }
          }
        }
      }
      result
    }
    else{
      var res0 = crossRefs1(cpts1, cpts2) ++ crossRefs1(cpts2, cpts1)
      // remove duplicates
      var result = List[Array[State]]()
      for(states <- res0){
        if(!result.exists(states1 => states1.sameElements(states)))
          result ::= states
      }
      result
    }
  }

  /** All cross references between cpts1 and cpts2 that involve a component c2
    * of cpts2 that is referenced by cpts1(0). */
  @inline private def crossRefs1(cpts1: Array[State], cpts2: Array[State])
      : List[Array[State]] = {
    var result = List[Array[State]](); val c1 = cpts1(0); var j = 0
    // References from c1 to components of cpts2
    while(j < cpts2.length){
      val c2 = cpts2(j); j += 1
      if(! contains(cpts1, c2) && c1.hasIncludedParam(c2.family, c2.id)){
        if(! contains(cpts2, c1)) result ::= Array(c1,c2)
        // Cross references from other components of cpts1 to c2, or vice versa
        for(j <- 1 until cpts1.length){
          val c11 = cpts1(j)
          if(!contains(cpts2, c11) && c11.hasIncludedParam(c2.family, c2.id))
            result ::= Array(c11, c2)
          if(c2.hasIncludedParam(c11.family, c11.id)) result ::= Array(c2, c11)
        }
      }
    }
    result
  }

  /** Make a bitmap representing the identities in cpts. */
  def makeIdsBitMap(cpts: Array[State]): BitMap = {
    val bitMap = newBitMap
    var i = 0
    while(i < cpts.length){
      val (f,id) = cpts(i).componentProcessIdentity
      bitMap(f)(id) = true; i += 1
    }
    bitMap
  }

  /** For each (t,i), the index of the component in cpts that has (t,i) as its
    * identity, or -1 if there is no such. */
  def makeIdsIndexMap(cpts: Array[State]): Array[Array[Int]] = {
    val indexMap = Array.tabulate(numTypes)(t => Array.fill(typeSizes(t))(-1))
    for(ix <- 0 until cpts.length){
      val (t,id) = cpts(ix).componentProcessIdentity
      indexMap(t)(id) = ix
    }
    indexMap
  }

  /** For each (t,i), the indices of the components c in cpts such that (t,i) is
    * a reference of c but not its identity. */
  def makeRefsIndexMap(cpts: Array[State]): Array[Array[List[Int]]] = {
    val indexMap = Array.tabulate(numTypes)(t => 
      Array.fill(typeSizes(t))(List[Int]()))
    for(ix <- 0 until cpts.length){
      val c = cpts(ix); val (idt,id) = c.componentProcessIdentity
      for(j <- 1 until c.length){
        val (t,x) = c.processIdentity(j)
        if(!isDistinguished(x) && (t != idt || x != id)) indexMap(t)(x) ::= ix
      }
    }
    indexMap
  }

  /** Remove identities of components in cpts from bitMap. */
  def removeIdsFromBitMap(cpts: Array[State], bitMap: BitMap) = {
    var i = 0
    while(i < cpts.length){
      val st = cpts(i); i += 1; bitMap(st.family)(st.id) = false
    }
  }

  /** Remove all parameters of cpts from bitMap. */
  def removeParamsFromBitMap(cpts: Array[State], bitMap: BitMap) = {
    var i = 0
    while(i < cpts.length){
      val st = cpts(i); i += 1; val pids = st.processIdentities; var j = 0
      while(j < pids.length){
        val (t,id) = pids(j); j += 1; if(id >= 0) bitMap(t)(id) = false
      }
    }
  }

  /** All included components referenced by cpts(0) but not in cpts. */
  def missingRefs(cpts: Array[State]): List[ProcessIdentity] = {
    val princ = cpts(0); val refs = princ.processIdentities
    var missing = List[ProcessIdentity](); var i = 1
    while(i < refs.length){
      if(princ.includeParam(i)){
        val ref = refs(i)
        if(!isDistinguished(ref._2) &&
          !cpts.exists(c => c.componentProcessIdentity == ref)) // IMPROVE
          missing ::= ref
      }
      i += 1
    }
    missing
  }

  @inline def mkHash(start: Int = 0, cpts: Array[State]) = {
    var h = start; var i = 0; var n = cpts.length
    while(i < n){ h = h*71+cpts(i).hashCode; i += 1 }    
    h 
  }

  /** Comparison function. */
  @inline def compare(cpts1: Array[State], cpts2: Array[State]): Int = {
    val len = cpts1.length; val lenComp = len - cpts2.length
    if(lenComp != 0) lenComp
    else{
      var i = 0
      while(i < len && cpts1(i) == cpts2(i)) i += 1
      if(i == len) 0 else cpts1(i).compare(cpts2(i))
    }
  }

  /** Is cpts1 < cpts2 according to compare? */
  def lessThan(cpts1: Array[State], cpts2: Array[State]): Boolean = 
    compare(cpts1, cpts2) < 0
}
