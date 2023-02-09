package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper

import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet}

/** Operations concerned with unifying states or views. */
object Unification{
  /** Main functions:
    * 
    * allUnifs      (called from EffectOnUnification)
    * |--unify      (called from Extendability.findReferencingView)
    * 
    * combine1      (called from EffectOnUnification.extendUnif,
    * |                 makeSecondaryInducedTransitions)
    * |--getCombiningMaps (called from EffectOnUnification.extendUnifSingleRef)
    * 
    * remapToJoin      (called from MissingCommon)
    * |--getCombiningMaps
    */

  /** Try to extend map to map' such that map'(st2) = st1.
    * Note: map is unchanged.
    * @return the new map, or null if unsuccessful. */
  @inline def unify(map: RemappingMap, st1: State, st2: State): RemappingMap = {
    // println(s"unify(${showRemappingMap(map)}, $st1, $st2)")
    if(st1.cs != st2.cs) null // false
    else{
      val map1 = Remapper.cloneMap(map)
      val ok = unify1(map1, st1, st2)
      // val ids1 = st1.ids; val ids2 = st2.ids
      // val len = ids1.length; val typeMap = st1.typeMap
      // assert(st1.family == st2.family && st2.typeMap == typeMap && 
      //   ids2.length == len)
      // // Iterate through the parameters; ok indicates if matching successful
      // // so far.
      // var i = 0; var ok = true
      // while(i < len && ok){
      //   val id1 = ids1(i); val id2 = ids2(i); val t = typeMap(i)
      //   if(isDistinguished(id1) || isDistinguished(id2)) ok = id1 == id2
      //   else if(map1(t)(id2) < 0){
      //     if(map1(t).contains(id1)) ok = false // must preserve injectivity 
      //     else map1(t)(id2) = id1 // extend map
      //   }
      //   else ok = map1(t)(id2) == id1
      //   i += 1
      // }
      if(ok) map1 else { Pools.returnRemappingRows(map1); null }
    }
  }

  /** Try to extend map such that map(st2) = st1.  Return true if
    * successful. Pre: st1.cs = st2.cs.  Note: mutates map. */
  @inline private 
  def unify1(map: RemappingMap, st1: State, st2: State): Boolean = {
    require(st1.cs == st2.cs)
    val ids1 = st1.ids; val ids2 = st2.ids
    val len = ids1.length; val typeMap = st1.typeMap
    assert(st1.family == st2.family && st2.typeMap == typeMap &&
      ids2.length == len)
    // Iterate through the parameters; ok indicates if matching successful
    // so far.
    var i = 0; var ok = true
    while(i < len && ok){
      val id1 = ids1(i); val id2 = ids2(i); val t = typeMap(i)
      if(isDistinguished(id1) || isDistinguished(id2)) ok = id1 == id2
      else if(map(t)(id2) < 0){
        if(map(t).contains(id1)) ok = false // must preserve injectivity
        else map(t)(id2) = id1 // extend map
      }
      else ok = map(t)(id2) == id1
      i += 1
    }
    ok
  }

  /** Try to extend map such that map(st2) = st1.  Return true if
    * successful. Pre: st1.cs = st2.cs.  Note: mutates map. */
  def extendToUnify(map: RemappingMap, st1: State, st2: State): Boolean = 
    st1.cs == st2.cs && unify1(map, st1, st2)

  /** The result of a unification, giving the indices of components that have
    * been unified.  A pair (j,i) indicates that cv.components(j) has been
    * unified with pre.components(i).  */ 
  type UnificationList = List[(Int,Int)]

  /** The result type of allUnifs. */ 
  private type AllUnifsResult = ArrayBuffer[(RemappingMap, UnificationList)]

  private def show(allUs: AllUnifsResult) = 
    allUs.map{case(map,us) => "("+Remapper.show(map)+", "+us+")"}.mkString("; ")

  /** All ways of extending map0 to unify components of cv with components of
    * pre; but don't unify the two principal components if !singleRef.  
    * 
    * For each combination of unifications, a remapping map so that if c =
    * cv.components(j) is unified with preC = pre.components(i), them map0(c)
    * = preC, and (j,i) is included in the UnificationList.
    * 
    * The maps returned are distinct.  */
  def allUnifs(pre: Concretization, cv: ComponentView) //cpts: Array[State]) 
      : AllUnifsResult = {
    require(pre.servers == cv.servers)
    val cpts = cv.components; val preCpts = pre.components
    val map0 = pre.servers.remappingMap1(cv.getParamsBound)
    // Map from identities to the index of the corresponding component in
    // preCpts, if any, otherwise -1.
    // val preCptsIndexMap = pre.idsIndexMap // State.indexMap(preCpts)
    val result = new AllUnifsResult // holds final result

    // Extend map and unifs to cpts[from..), adding results to results.  Each
    // call either uses map in the result or recycles it.
    def allUnifsRec(map: RemappingMap, from: Int, unifs: UnificationList)
        : Unit = {
      if(from == cpts.length) result += ((map, unifs))
      else{
        val c = cpts(from)

        // Try to unify c with preCpts(i)
        @inline def tryUnify(i: Int): Unit = {
          val map1 = unify(map,  preCpts(i), c) // map1 is a new map
          if(map1 != null){
            // check that map was not extended on any identity of a component
            // in cpts[0..from) to match a component in preCpts: if so, we
            // should have unified earlier.
            var j = 0; var ok = true
            while(j < from && ok){
              val cj = cpts(j); val f = cj.family; val id = cj.ids(0)
              // val (f,id) = cpts(j).componentProcessIdentity
              val id1 = map1(f)(id)
              // Check map not extended on (f,id), or (f,id1) doesn't match an
              // identity in preCpts
              ok = id1 == map(f)(id) || pre.idsIndexMap(f)(id1) < 0
              j += 1
            }
            if(ok) allUnifsRec(map1, from+1, (from,i)::unifs)
          } // end of if
        } // end of tryUnify

        // Test if (fc,fId) already mapped to a component of preCpts.  If so,
        // try to unify those components; but don't unify the two principals
        // if !singleRef (that would just recreate the same transition).
        val fc = c.family; val id1 = map(fc)(c.id)
        val ix = if(id1 < 0) -1 else pre.idsIndexMap(fc)(id1)
        if(ix >= 0){ 
          if(singleRef || from > 0 || ix > 0) tryUnify(ix)
          Pools.returnRemappingRows(map) // finished with map
        }
        else{
          // Try to unify with each component in turn, but don't unify the two
          // principals if !singleRef (that would just recreate the same
          // transition).
          var i = if(from == 0 && !singleRef) 1 else 0
          while(i < preCpts.length){ tryUnify(i); i += 1 }
          // No unifications for c
          allUnifsRec(map, from+1, unifs)
        }
      }
    } // end of allUnifsRec

    allUnifsRec(map0, 0, List())
    result
  }

  // A representation of map |> post.servers
  import ServersReducedMap.ReducedMap 

  /** Result returned from combine1.  Each entry is of the form (map, unifs)
    * where: map is a remapping map; and unifs is a UnificationList that
    * contains (j,i) whenever cv.components(j) unifies with
    * pre.components(i). */
  type CombineResult = ArrayBuffer[(RemappingMap,  UnificationList)]

  /** All ways of remapping cpts, consistent with map.  Parameters not in dom
    * map can be mapped: (1) to values of otherArgs, but, in the case of
    * identities, only those included in bitMap; or (2) to fresh values
    * starting from nextArg.  Pair each resulting map with unifs, and add to
    * result.
    * 
    * IMPROVE: do not remap components with indexes in map fst unifs.
    * 
    * map, otherArgs and nextArg are treated mutable, but all updates are
    * backtracked. */
  def combine1(
    map: RemappingMap, otherArgs: OtherArgMap, bitMap: BitMap, 
    nextArg: NextArgMap, unifs: UnificationList, 
    cpts: Array[State], result: CombineResult)
      : Unit = {
    if(false && debugging){
      assert(Remapper.isInjective(map), Remapper.show(map))
      // Check otherArgs disjoint from ran map
      // for(f <- 0 until numTypes; id <- otherArgs(f);
      //     id1 <- 0 until map(f).length)
      //   assert(map(f)(id1) != id)
    }
    val maps = getCombiningMaps(map, otherArgs, bitMap, nextArg, cpts)
    for(map1 <- maps){ 
      result += ((map1, unifs /*, null*/))
    }
  }

  /** Find all ways of remapping cpts, consistent with map.  Parameters not in
    * dom map can be mapped: (1) to values of otherArgs, but, in the case of
    * identities, only those included in bitMap; or (2) to fresh values
    * starting from nextArg. 
    * 
    * map, otherArgs and nextArg are treated mutable, but all updates are
    * backtracked. */
  @inline def getCombiningMaps(
    map: RemappingMap, otherArgs: OtherArgMap, bitMap: BitMap, 
    nextArg: NextArgMap, cpts: Array[State])
      : ArrayBuffer[RemappingMap] = {
    if(false && debugging){ // IMPROVE
      assert(Remapper.isInjective(map), Remapper.show(map))
      for(f <- 0 until numTypes) assert(otherArgs(f) == otherArgs(f).distinct)
      // Check otherArgs disjoint from ran map
      for(f <- 0 until numTypes; id <- otherArgs(f); 
          id1 <- 0 until map(f).length)
        assert(map(f)(id1) != id)
    }
    val result = new ArrayBuffer[RemappingMap]

    // Recursively remap cpts(i).args[j..), then cpts[i+1..).
    def rec(i: Int, j: Int): Unit = {
      if(false && debugging) // Following is very expensive
        assert(Remapper.isInjective(map), Remapper.show(map))
      if(i == cpts.length) result += Remapper.cloneMap(map)
      else{
        val c = cpts(i); val ids = c.ids
        if(j == ids.length) // End of this component; move to next component
          rec(i+1, 0)
        else {
          val id = ids(j); val f = c.typeMap(j)
          // Maybe rename (f, id)
          if(isDistinguished(id) || map(f)(id) >= 0) rec(i, j+1) // just move on
          else{
            // Is (f,id) an identity of any component? 
            var ii = 0; var isIdentity = false
            while(ii < cpts.length && !isIdentity){
              val st = cpts(ii); isIdentity = st.family == f && st.id == id
              ii += 1
            }
            // Case 1: map id to an element id1 of otherArgs(f) (respecting
            // bitMap if (f,id) is an identity).
            var toDoIds = otherArgs(f); var doneIds = List[Identity]()
            // We still need to map id to each element of toDoIds; doneIds
            // represents those done already.
            while(toDoIds.nonEmpty){
              val id1 = toDoIds.head; toDoIds = toDoIds.tail
              if(!isIdentity || bitMap(f)(id1)){
                otherArgs(f) = append1(doneIds, toDoIds) // temporary update (*)
                map(f)(id) = id1 // temporary update (+)
                rec(i, j+1)
                map(f)(id) = -1  // backtrack (+)
              }
              doneIds = id1::doneIds // order doesn't matter
            } // end of while loop
            otherArgs(f) = doneIds // undo (*)

            // Case 2: map id to nextArg(f)
            val id1 = nextArg(f)
            map(f)(id) = id1; nextArg(f) += 1 // temporary updates (+)
            rec(i, j+1)
            nextArg(f) -= 1; map(f)(id) = -1 // backtrack (+)
          }
        }
      }
    } // end of rec

    rec(0, 0); result
  }

  /** Remap c, as identity function on parameters of servers and princ1, but
    * mapping other parameters either to other parameters of cpts1.tail or
    * cpts2, or to fresh values.
    * 
    * There is an existing view servers || princ1 || c, and we want to find if
    * there is a view servers || cpts2(0) || c' for c' a renaming of c. 
    * 
    * Pre: princ1 has a reference to c. */ 
// IMPROVE comment
  def remapToJoin(servers: ServerStates, princ1: State, 
    cpts1: Array[State], cpts2: Array[State], c: State)
      : Array[State] = {
    require(singleRef)
    require(princ1.processIdentities.contains(c.componentProcessIdentity))
    // We look to use combineX, although some of the parameters there aren't
    // used.  IMPROVE?
    // Identity map on parameters of servers and princ1; and next args to use
    val map0 = servers.remappingMap; val nextArgMap = servers.nextArgMap
    for((f,id) <- princ1.processIdentities; if !isDistinguished(id)){
      map0(f)(id) = id; nextArgMap(f) = nextArgMap(f) max (id+1)
    }
    // Make otherArgMap, with parameters of not in map0, maintaining
    // nextArgMap
    val otherArgs = Remapper.newOtherArgMap
    for(cpt2 <- cpts1.tail ++ cpts2; (f,id) <- cpt2.processIdentities)
      if(!isDistinguished(id) && map0(f)(id) < 0 && !otherArgs(f).contains(id)){
        // Note: we use map0(f)(id) < 0 as a proxy for !map0(f).contains(id)
        // here, as map0 is a partial identity mapping.
        assert(!map0(f).contains(id)) // IMPROVE
        otherArgs(f) ::= id; nextArgMap(f) = nextArgMap(f) max (id+1)
      }
    // Note: the bitmap is empty: c's id should not be remapped, by precondition.
    val maps = 
      getCombiningMaps(map0, otherArgs, emptyBitMap, nextArgMap, Array(c))
    val result = new Array[State](maps.length); var i = 0
    while(i < maps.length){
      val map = maps(i); result(i) = Remapper.applyRemappingToState(map, c)
      i += 1; Pools.returnRemappingRows(map)
    }
    Pools.returnRemappingRows(map0)
    result
  }

  /** An empty bit map, for use in remapToJoin. */
  private val emptyBitMap = newBitMap

  /** New version of above, mapping parameters of c to parameters of a secondary
    * component c2 of cpts1 or cpts2 only if there is already a cross
    * reference between c and c2 (in either direction). */ 
  def newRemapToJoin(servers: ServerStates, princ1: State, 
    cpts1: Array[State], cpts2: Array[State], c: State)
      : Array[State] = {
    require(singleRef)
    require(princ1.processIdentities.contains(c.componentProcessIdentity))
    // Identity map on parameters of servers and princ1; and next args to use
    val map0 = servers.remappingMap; val nextArg = servers.nextArgMap
// IMPROVE: limit to params of c
    for((t,id) <- princ1.processIdentities; if !isDistinguished(id)){
      assert(id <= nextArg(t));
      map0(t)(id) = id; nextArg(t) = nextArg(t) max (id+1)
    }
    // Params not to map onto; include params of servers and princ1
    val omit = Array.tabulate(numTypes)(t => (0 until nextArg(t)).toList)
    // Calculate nextArg
    for(st <- cpts1.tail ++ cpts2; t <- 0 until numTypes)
      nextArg(t) = nextArg(t) max st.getParamsBound(t)
    //println("nextArg = "+nextArg.mkString(", "))
    // Params of c
    val cIds = c.processIdentities
    val (t,id) = c.componentProcessIdentity; assert(map0(t)(id) == id)
    // Secondary cpts
    val secondaries: Array[State] = cpts1.tail++cpts2.tail
    val stateBuffer = new ArrayBuffer[State]

    /* If there is a cross reference between map(c) and a secondary component c2
     * with index not in doneSecondaries, extend map to map to parameters of
     * c2; and recurse.  Add results of mapping c in such a way to
     * stateBuffer. */
    def rec(map: RemappingMap, doneSecondaries: List[Int]): Unit = {
      // Try to find a reference between a secondary cpt and map(c)
      var i = 0; var found = false
      while(i < secondaries.length && !found){
        if(!doneSecondaries.contains(i)){
          val st1 = secondaries(i)
          if(st1.hasRef(t,id)) found = true         // reference from st1 to c 
          else{
            // Search for ref from map(c) to st1
            var j = 1; val (t1,id1) = st1.componentProcessIdentity
            while(j < cIds.length && !found){
              val (t2,id2) = cIds(j); j += 1
              found = (t2 == t1 && !isDistinguished(id2) && map(t2)(id2) == id1)
            }
          }
        } // end of outer if
        if(!found) i += 1
      } // end of while

      if(found){
        //println("Extending "+Remapper.show(map)+" for "+secondaries(i))
        //println("omit = "+omit.mkString("; "))
        val oldOmit = omit.clone                         // store (*)
        val ab1 = extendToCpt(map, c, secondaries(i), omit)
        //println("Result: "+ab1.map(Remapper.show))
        for(map1 <- ab1) rec(map1, i::doneSecondaries)
        for(t <- 0 until numTypes) omit(t) = oldOmit(t)  // backtrack to (*)
      }
      else{        // Extend map to map to fresh params, and apply to c
        val map1 = Remapper.cloneMap(map)
        // println("map1 = "+Remapper.show(map1))
        for(t <- 0 until numTypes){
          var next = nextArg(t)
          for((t1,x) <- cIds; if t1 == t && !isDistinguished(x))
            if(map1(t)(x) < 0){ map1(t)(x) = next; next += 1 }
        }
        // Remapper.mapUndefinedToFresh(map1, nextArg)
        //println("extended: "+Remapper.show(map1))
        stateBuffer += Remapper.applyRemappingToState(map1, c)
      }
    } // end of rec

    // Extend map to params of cpts2(0)
    val ab1 = extendToCpt(map0, c, cpts2(0), omit)
    for(map1 <- ab1) rec(map1, List())
    stateBuffer.toArray
  }

  /** Extend map0, mapping parameters of c, other than its identity, to
    * parameters of st other than omit.  Add each to ab.  Also add parameters
    * of st to omit. */
  @inline private def extendToCpt(
    map0: RemappingMap, c: State, st: State, omit: Array[List[Identity]])
      : ArrayBuffer[RemappingMap] = {
    // Parameters of st not in omit
    val otherArgs = Remapper.newOtherArgMap
    for((f,id) <- st.processIdentities; if !isDistinguished(id))
      if(!omit(f).contains(id) && !otherArgs(f).contains(id))
        otherArgs(f) ::= id
    val cIds = c.ids; val cLen = cIds.length; val typeMap = c.typeMap
    val ab = new ArrayBuffer[RemappingMap]

    /* Extend map0 over cIds[j..cLen), mapping to values in otherArgs, or not.
     * Add each resulting map to ab.  Roll back updates to map0 and
     * otherArgs. */
    def rec(j: Int): Unit = {
      if(j == cLen) ab += Remapper.cloneMap(map0)
      else{
        val x = cIds(j); val t = c.typeMap(j)
        // Maybe remap (t,x)
        if(!isDistinguished(x) && map0(t)(x) < 0){
          // map (t,x) to each parameter of otherArgs(t)
          var toDoIds = otherArgs(t); var doneIds = List[Identity]()
          // Still need to map to each param of toDoIds; doneIds is those ids
          // already done.
          while(toDoIds.nonEmpty){
            val id1 = toDoIds.head; toDoIds = toDoIds.tail
            otherArgs(t) = append1(doneIds, toDoIds) // temporary update (*)
            map0(t)(x) = id1                         // temporary update (+)
            rec(j+1)                                 // rename rest
            map0(t)(x) = -1                          // backtrack (+)
            doneIds ::= id1 // order doesn't matter
          } // end of while
          otherArgs(t) = doneIds                     // backtrack (*)
        } // end of if
        // Also leave x unmapped 
        rec(j+1)              
      }
    } // end of rec

    require(map0(typeMap(0))(cIds(0)) >= 0) // c's id already remapped
    rec(1) // calculate the extensions
    // Add parameters of st to omit
    for(t <- 0 until numTypes) omit(t) = omit(t) ++ otherArgs(t)
    ab
  }

  // private def extendToCpts(map0: RemappingMap, c: State, sts: List[State])
  //     : Array[RemappingMap] = {
  //   if(sts.isEmpty) Array(map0)
  //   else{
  //     val maps1 = extendToCpt(map0, c, sts.head, ???).toArray
  //     maps1.flatMap(map1 => extendToCpts(map1, c, sts.tail))
  //   }
  // }


  /** Hooks for testing. */
  trait Tester{
    type AllUnifsResult = Unification.AllUnifsResult
    protected val allUnifs = Unification.allUnifs _
  }


}
