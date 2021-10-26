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
    * combine1      (called from EffectOnUnification)
    * |--combineX
    * 
    * remapToJoin      (called from MissingCommon)
    * |--combineX
    */

  /** Try to extend map to map' such that map'(st2) = st1.
    * Note: map is unchanged.
    * @return the new map, or null if unsuccessful. */
  def unify(map: RemappingMap, st1: State, st2: State): RemappingMap = {
    // println(s"unify(${showRemappingMap(map)}, $st1, $st2)")
    if(st1.cs != st2.cs) null // false
    else{
      val map1 = Remapper.cloneMap(map)
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
        else if(map1(t)(id2) < 0){
          if(map1(t).contains(id1)) ok = false // must preserve injectivity 
          else map1(t)(id2) = id1 // extend map
        }
        else ok = map1(t)(id2) == id1
        i += 1
      }
      if(ok) map1 else null 
    }
  }

  /** The result of a unification, giving the indices of components that have
    * been unified. */ 
  type UnificationList = List[(Int,Int)]

  /** The result type of allUnifs. */ 
  private type AllUnifsResult = ArrayBuffer[(RemappingMap, UnificationList)]

  private def show(allUs: AllUnifsResult) = 
    allUs.map{case(map,us) => "("+Remapper.show(map)+", "+us+")"}.mkString("; ")

  /** All ways of extending map0 to unify elements of cpts with elements of
    * preCpts, other than the two principal components.  
    * 
    * For each combination of unifications, map0 is extended to a mapping map
    * so that if c = cpts(j) is unified with preC = preCpts(i), them map0(c) =
    * preC, and (j,i) is included in the UnificationList.  */
  def allUnifs(
    map0: RemappingMap, preCpts: Array[State], cpts: Array[State]) 
      : AllUnifsResult = {
    // Map from identities to the index of the corresponding component in
    // preCpts, if any, otherwise -1.
    val preCptsIndexMap = State.indexMap(preCpts)
    val result = new AllUnifsResult // holds final result

    // Extend map and unifs to cpts[from..), adding results to results. 
    def allUnifsRec(map: RemappingMap, from: Int, unifs: UnificationList)
        : Unit = {
      if(from == cpts.length) result += ((map, unifs))
      else{
        val c = cpts(from)

        // Try to unify c with preCpts(i)
        @inline def tryUnify(i: Int): Unit = {
          val map1 = unify(map,  preCpts(i), c)
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
              ok = id1 == map(f)(id) || preCptsIndexMap(f)(id1) < 0
              j += 1
            }
            if(ok) allUnifsRec(map1, from+1, (from,i)::unifs)
          } // end of if
        } // end of tryUnify

        // Test if (fc,fId) already mapped to a component of preCpts
        val fc = c.family; val id1 = map(fc)(c.id)
        val ix = if(id1 < 0) -1 else preCptsIndexMap(fc)(id1)
        if(ix >= 0) tryUnify(ix) 
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

  /** Bit map, indexed by process identities. */
  // type BitMap = Array[Array[Boolean]]

  

  /** Result returned from combine1.  Each entry represents a remapping map, its
    * application to cv.components, and a UnificationList that contains (j,i)
    * whenever cv.components(j) unifies with pre.components(i). */
  type CombineResult = ArrayBuffer[(RemappingMap, Array[State], UnificationList)]

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
    val res0 = new ArrayBuffer[RemappingMap]
    getCombiningMaps(map, otherArgs, bitMap, nextArg, cpts, res0)
    for(map1 <- res0) 
      result += ((map1, Remapper.applyRemapping(map1, cpts), unifs))
  }


  /** Find all ways of remapping cpts, consistent with map.  Parameters not in
    * dom map can be mapped: (1) to values of otherArgs, but, in the case of
    * identities, only those included in bitMap; or (2) to fresh values
    * starting from nextArg.  Each such map is added to result.
    * 
    * map, otherArgs and nextArg are treated mutable, but all updates are
    * backtracked. */
  @inline def getCombiningMaps(
    map: RemappingMap, otherArgs: OtherArgMap, bitMap: BitMap, 
    nextArg: NextArgMap, cpts: Array[State], result: ArrayBuffer[RemappingMap])
      : Unit = {
    if(debugging){ // IMPROVE
      assert(Remapper.isInjective(map), Remapper.show(map))
      for(f <- 0 until numTypes) assert(otherArgs(f) == otherArgs(f).distinct)
      // Check otherArgs disjoint from ran map
      for(f <- 0 until numTypes; id <- otherArgs(f); 
          id1 <- 0 until map(f).length)
        assert(map(f)(id1) != id)
    }

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

    rec(0, 0)
  }
  /** Remap c, as identity function on parameters of servers and princ1, but
    * mapping other parameters either to other parameters of cpts2, or to
    * fresh values.
    * 
    * There is an existing view servers || princ1 || c, and we want to find if
    * there is a view servers || cpts2(0) || c' for c' a renaming of c. 
    * 
    * Pre: princ1 has a reference to c. */ 
// IMPROVE comment
  def remapToJoin(
    servers: ServerStates, princ1: State, cpts2: Array[State], c: State)
      : ArrayBuffer[State] = {
    require(singleRef)
    require(princ1.processIdentities.contains(c.componentProcessIdentity))
    // We look to use combineX, although some of the parameters there aren't
    // used.  IMPROVE?
    // Identity map on parameters of servers and princ1; and next args to use
    val map0 = servers.remappingMap; val nextArgMap = servers.nextArgMap
    for((f,id) <- princ1.processIdentities; if !isDistinguished(id)){
      map0(f)(id) = id; nextArgMap(f) = nextArgMap(f) max (id+1)
    }
    // Make otherArgMap, with parameters of princ2 not in map0, maintaining
    // otherArgMap
    val otherArgs = Remapper.newOtherArgMap
    for(cpt2 <- cpts2; (f,id) <- cpt2.processIdentities)
      if(!isDistinguished(id) && map0(f)(id) < 0 && !otherArgs(f).contains(id)){
        assert(!map0(f).contains(id)) // IMPROVE
        otherArgs(f) ::= id; nextArgMap(f) = nextArgMap(f) max (id+1)
      }
    // println(s"otherArgs = "+otherArgs.mkString(", "))
    val result = new ArrayBuffer[RemappingMap] // CombineResult
    // the bitmap is empty: c's id should not be remapped, by precondition.
    getCombiningMaps(map0, otherArgs, newBitMap, nextArgMap, Array(c), result)
    result.map{ case map => Remapper.applyRemappingToState(map, c) }
  }

  /** Hooks for testing. */
  trait Tester{
    type AllUnifsResult = Unification.AllUnifsResult
    protected val allUnifs = Unification.allUnifs _
  }


}
