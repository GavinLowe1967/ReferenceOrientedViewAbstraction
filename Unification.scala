package ViewAbstraction.RemapperP

import ViewAbstraction._
import ViewAbstraction.RemapperP._

import scala.collection.mutable.ArrayBuffer

/** Operations concerned with unifying states or views. */
object Unification{
  import Remapper.{RemappingMap,NextArgMap,OtherArgMap}

  var combineCount = 0L
  var renameXCount = 0L
  var combine2Count = 0L

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

  /** Unifications between the components of two views, giving the indices of
    * components that are unified with one another. */
  type Unifications = List[(Int, Int)]

  /** Find the index k of cpts with identity pid.  Return -1 if no such index. */
  @inline private def find(cpts: Array[State], f: Family, id: Identity) = {
    // Search backwards to facilitate default result of -1
    var k = cpts.length-1
    while(k >= 0 && !cpts(k).hasPID(f,id)) k -= 1
    k
    // var k = -1; var i = 0
    // while(i < cpts.length){
    //   if(cpts(i).hasPID(f,id)){ assert(k < 0); k = i } // IMPROVE
    //   i += 1
    // }
    // k
  }

  /** Update otherArgs to be disjoint from ran map. */
  @inline private def makeDisjoint(otherArgs: OtherArgMap, map: RemappingMap) = {
    var f1 = 0
    while(f1 < numTypes){
      otherArgs(f1) = otherArgs(f1).filter(id => !map(f1).contains(id))
      f1 += 1
    }
  }

  @inline private 
  def restoreOtherArgMap(otherArgs: OtherArgMap, oldOtherArgs: OtherArgMap) = {
    var f1 = 0
    while(f1 < numTypes){
      otherArgs(f1) = oldOtherArgs(f1); f1 += 1
    }
  }

  type CombineResult = ArrayBuffer[(Array[State], Unifications)]

  /** Extend map, in all possible ways, to remap cpts2 so as to be compatible
    * with cpts1.  Each parameter (f,p), not in the domain of map, can be
    * mapped to an element of otherArgs(f) (a subset of the parameters of
    * cpts1), or a fresh value given by nextArg(f).  If the jth identity
    * parameter of cpts2 maps to the kth identity parameter of cpts1, then the
    * corresponding States much match, and the pair (k,j) is included in the
    * Unifications returned.  Called by combine.  See
    * RemapperTest.combine1Test for examples.
    * 
    * @param map the RemappingMap that gets extended.  Cloned before being 
    * mutated.
    * @param nextArg a NextArgMap giving the next fresh parameter to use for 
    * each type.  For each type, at least one more than the maximum of the
    * corresponding parameters of cpts1 and elements of map0 and otherArgs.
    * Used mutably, but each update is backtracked.
    * @param otherArgs for each type, a list of other values that a parameter
    * can be mapped to.  For each type, disjoint from the range of the
    * corresponding element of map0.  Used mutably, but each update is
    * backtracked.
    * @return all resulting remappings of cpts2 together with the 
    * unifications. */
  private[RemapperP]
  def combine1(map: RemappingMap, nextArg: NextArgMap,
      otherArgs: OtherArgMap, cpts1: Array[State], cpts2: Array[State])
      : CombineResult = {
    val result = new ArrayBuffer[(Array[State], Unifications)]
    combine2(map, nextArg, otherArgs, cpts1, cpts2, result, 0, 0, List())
    result
  }

  /** As combine1, except extending map to remap cpts2(j).ids[i..) and then
    * cpts2[j+1..), adding all results to results. */
  private[RemapperP]
  def combine2(map: RemappingMap, nextArg: NextArgMap,
    otherArgs: OtherArgMap, cpts1: Array[State], cpts2: Array[State],
    result: CombineResult, i: Int, j: Int, unifs: Unifications): Unit 
  = {
    /* Rename (f,id) to id1; if this is the identity parameter, then
     * unify with corresponding component in cpts1 if there is one. */
    @inline def renameX(f: Family, id: Identity, id1: Identity) = {
      renameXCount += 1
      val idX = map(f)(id) // store for backtracking
      // If i==0, this is the identity; see if any component of cpts1
      // matches (f, id1)
      val k = if(i > 0) -1 else find(cpts1, f, id1)
      if(k >= 0){
        map(f)(id) = id1 // temporary update (*)
        val map2 = unify(map, cpts1(k), cpts2(j))
        if(map2 != null){
          val oldOtherArgs = otherArgs.clone // store
          // Update otherArgs to be disjoint from ran map2.
          makeDisjoint(otherArgs, map2) // (+)
          combine2(map2, nextArg, otherArgs, cpts1, cpts2, result,
            0, j+1, (k,j)::unifs)
          restoreOtherArgMap(otherArgs, oldOtherArgs) // Undo (+)
        }
        map(f)(id) = idX // backtrack (*)
      } // end of if k >= 0
      else{ // No cpt of cpts1 matched; move on
        map(f)(id) = id1  // temporary update (*)
        combine2(map, nextArg, otherArgs, cpts1, cpts2, result, i+1, j, unifs)
        map(f)(id) = idX // backtrack (*)
      }
    } // end of renameX

    combine2Count += 1
    if(j == cpts2.length)
      result += ((Remapper.applyRemapping(map, cpts2), unifs))  // base case
    else{
      val c = cpts2(j); val ids = c.ids; val typeMap = c.typeMap
      if(i == ids.length) // End of this component; move to next component
        combine2(map, nextArg, otherArgs, cpts1, cpts2, result, 0, j+1, unifs)
      else{
        val id = ids(i); val f = typeMap(i)
        if(isDistinguished(id))  // just move on
          combine2(map, nextArg, otherArgs, cpts1, cpts2, result, i+1, j, unifs)
        else{ // rename (f, id)
          // Case 1: map id to the corresponding value idX in map, if any;
          // otherwise to an element id1 of otherArgs(f).
          val idX = map(f)(id)
          if(idX < 0){
            // Call renameX for each id1 in otherArgs(f), with id1 removed
            // from otherArgs(f).  toDoIds represents the identities still
            // to deal with; doneIds is those already done.
            var toDoIds = otherArgs(f); var doneIds = List[Identity]()
            // Profiler.count("rec"+toDoIds.length): 0: 5%; 1: 60%; 2: 30%; 3: 5%
            while(toDoIds.nonEmpty){
              val id1 = toDoIds.head; toDoIds = toDoIds.tail
              otherArgs(f) = doneIds++toDoIds // temporary update (*)
              renameX(f, id, id1)
              doneIds = id1::doneIds //  order doesn't matter
            }
            otherArgs(f) = doneIds // undo (*)
          }
          else renameX(f, id, idX)

          // Case 2: map id to nextArg(f)
          if(idX < 0){
            val id1 = nextArg(f); nextArg(f) += 1 // temporary update (+)
            map(f)(id) = id1 // (+)
            combine2(map, nextArg, otherArgs, cpts1, cpts2, result, 
              i+1, j, unifs) // Move on to next parameter
            nextArg(f) -= 1; map(f)(id) = idX  // undo (+)
          }
        }
      }
    }
  }

  /** Try to combine two component views.  Produce all pi(v2), for remapping pi,
    * such that v1 U pi(v2) makes sense, i.e. agree on common components.  If
    * the jth identity parameter of v2 maps to the kth identity parameter of
    * v1, then the corresponding States much match, and the pair (k,j) is
    * included in the Unifications returned. */
  def combine(v1: Concretization, v2: ComponentView)
      : ArrayBuffer[(Array[State], Unifications)] = {
    combineCount += 1
    // println(s"combine($v1, $v2)")
    val servers = v1.servers; require(v2.servers == servers)
    val components1 = v1.components; val components2 = v2.components
    // View.checkDistinct(components2)
    // The initial maps: map0 is the identity on the server parameters;
    // otherArgs gives parameters used in v1 but not the servers; nextArg
    // gives the next fresh parameters.
    val (map0, otherArgs, nextArg) = 
      Remapper.createCombiningMaps(servers, components1)

    if(false){      // IMPROVE: following checks are expensive
      var f = 0
      while(f < numTypes){
        // Check otherArgs(f) disjoint from ran(map0(f))
        var oa = otherArgs(f)
        while(oa.nonEmpty){
          require(!map0(f).contains(oa.head),
            s"combine1: otherArgs not disjoint from map0 for $f: "+
              map0(f).mkString("[",",","]")+"; "+otherArgs(f).mkString("[",",","]"))
          oa = oa.tail
        }
        // Check nextArg(f) holds next fresh value
        require(nextArg(f) > (
          if(otherArgs(f).isEmpty) map0(f).max
          else(map0(f).max max otherArgs(f).max)  ),
          s"combine1: nextArg($f) with incorrect value: "+nextArg(f)+"; "+
            map0(f).mkString("[",",","]")+"; "+otherArgs(f).mkString("[",",","]"))
        f += 1
      }
    } // end of if(false)

    combine1(map0, nextArg, otherArgs, components1, components2)
  }

  /** Try to combine two component views.  Produce all pi(v2), for remapping pi,
    * such that v1 U pi(v2) makes sense, i.e. agree on common components, and
    * a component of v2 unifies with some component of v1 such that the
    * corresponding entry in flags is true.  If the jth identity parameter of
    * v2 maps to the kth identity parameter of v1, then the corresponding
    * States much match, and the pair (k,j) is included in the Unifications
    * returned. */
  def combineWithUnification(
    v1: Concretization, flags: Array[Boolean], v2: ComponentView)
      : ArrayBuffer[(Array[State], Unifications)] = {
    val servers = v1.servers; require(v2.servers == servers)
    val components1 = v1.components; val components2 = v2.components
    // View.checkDistinct(components2); 
    require(components1.length == flags.length)
    val result = new ArrayBuffer[(Array[State], Unifications)]
    val (map0, otherArgs0, nextArg0) = 
      Remapper.createCombiningMaps(servers, components1)
    val otherArgs1 = new Array[List[Identity]](numTypes)
    val nextArg1 = new Array[Int](numTypes)

    var i = 0
    while(i < components1.length){
      if(flags(i)){
        val st1 = components1(i)
        // Try to unify st1 with a state of v2
        var j = 0
        while(j < components2.length){
          val st2 = components2(j)
          if(st1.cs == st2.cs){
            val map1 = unify(map0, st1, st2)
            if(map1 != null){
              //  make otherArgs1 and nextArg1 consistent with map1
              for(f <- 0 until numTypes){
                otherArgs1(f) = otherArgs0(f).filter(id => !map1(f).contains(id))
                nextArg1(f) = nextArg0(f) max (map1(f).max+1)
              }
              // IMPROVE:  don't remap st1?
              val res =
                combine1(map1, nextArg1, otherArgs1, components1, components2)
              assert(res.forall{case (_,unifs) => unifs.contains(i,j)})
              // Check no repetitions in res
              assert(res.forall{ case(sts,unifs) =>
                res.forall{ case(sts1,unifs1) =>
                  sts == sts1 || unifs != unifs1 || !sts.sameElements(sts1) } })
              result ++= res // IMPROVE
              // Note: result may contain repetitions, even though res doesn't.
            }
          }
          j += 1
        }
      }
      i += 1
    }
    result
  }

}
