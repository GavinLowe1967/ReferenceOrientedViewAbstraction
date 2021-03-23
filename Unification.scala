package ViewAbstraction.RemapperP

import ViewAbstraction._
import ViewAbstraction.RemapperP._

import ox.gavin.profiling.Profiler
import scala.collection.mutable.ArrayBuffer

/** Operations concerned with unifying states or views. */
object Unification{
  // import Remapper.{RemappingMap,NextArgMap}

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

  /** Find the index k of cpts with identity pid.  Return -1 if no such index. */
  @inline private def find(cpts: Array[State], f: Family, id: Identity) = {
    // Search backwards to facilitate default result of -1
    var k = cpts.length-1
    while(k >= 0 && !cpts(k).hasPID(f,id)) k -= 1
    k
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

  /** The result of a call to combine.  All remapped states, and the index of
    * the component in cpts1 that the principal of cpts2 gets mapped to, or -1
    * if none. */
  type CombineResult = ArrayBuffer[(Array[State], Int)]

  /** Extend map, in all possible ways, to remap cpts2 so as to be compatible
    * with cpts1.  Each parameter (f,p), not in the domain of map, can be
    * mapped to an element of otherArgs(f) (a subset of the parameters of
    * cpts1), or a fresh value given by nextArg(f).  If an identity of cpts2
    * maps to an identity of cpts1, then the corresponding parameters must
    * match.  Called by combine.  See RemapperTest.combine1Test for examples.
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
    * @return all resulting remappings of cpts2, together with the index of the
    * component of cpts1 that the principal of cpts2 maps to, if any,
    * otherwise -1. */
  private[RemapperP]
  def combine1(map: RemappingMap, nextArg: NextArgMap,
      otherArgs: OtherArgMap, cpts1: Array[State], cpts2: Array[State])
      : CombineResult = {
    val result = new CombineResult // ArrayBuffer[(Array[State], Int)]
    combine2(map, nextArg, otherArgs, cpts1, cpts2, result, 0, 0, -1)
    result
  }

  /** As combine1, except extending map to remap cpts2(j).ids[i..) and then
    * cpts2[j+1..), adding all results to results; unif0 is the index of the
    * component of cpts1 that the principal of cpts2 maps to, if any,
    * otherwise -1. */
  private[RemapperP]
  def combine2(map: RemappingMap, nextArg: NextArgMap,
    otherArgs: OtherArgMap, cpts1: Array[State], cpts2: Array[State],
    result: CombineResult, i: Int, j: Int, unif0: Int): Unit 
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
            0, j+1, if(j == 0){assert(unif0 < 0); k} else unif0)
          restoreOtherArgMap(otherArgs, oldOtherArgs) // Undo (+)
        }
        map(f)(id) = idX // backtrack (*)
      } // end of if k >= 0
      else{ // No cpt of cpts1 matched; move on
        map(f)(id) = id1  // temporary update (*)
        combine2(map, nextArg, otherArgs, cpts1, cpts2, result, i+1, j, unif0)
        map(f)(id) = idX // backtrack (*)
      }
    } // end of renameX

    combine2Count += 1
    if(j == cpts2.length)
      result += ((Remapper.applyRemapping(map, cpts2), unif0))  // base case
    else{
      val c = cpts2(j); val ids = c.ids; val typeMap = c.typeMap
      if(i == ids.length) // End of this component; move to next component
        combine2(map, nextArg, otherArgs, cpts1, cpts2, result, 0, j+1, unif0)
      else{
        val id = ids(i); val f = typeMap(i)
        if(isDistinguished(id))  // just move on
          combine2(map, nextArg, otherArgs, cpts1, cpts2, result, i+1, j, unif0)
        else{ // rename (f, id)
          // Case 1: map id to the corresponding value idX in map, if any;
          // otherwise to an element id1 of otherArgs(f).
          assert(id < map(f).length, 
            s"f = $f, id = $id, c = $c\ncpts1 = "+
              cpts1.map(_.toString0).mkString("; ")+
              "\ncpts2 = "+cpts2.map(_.toString0).mkString("; "))
          val idX = map(f)(id)
          if(idX < 0){
            // Call renameX for each id1 in otherArgs(f), with id1 removed
            // from otherArgs(f).  toDoIds represents the identities still
            // to deal with; doneIds is those already done.
            var toDoIds = otherArgs(f); var doneIds = List[Identity]()
            // Profiler.count("rec"+toDoIds.length): 0: 5%; 1: 60%; 2: 30%; 3: 5%
            while(toDoIds.nonEmpty){
              val id1 = toDoIds.head; toDoIds = toDoIds.tail
              otherArgs(f) = append1(doneIds, toDoIds) // doneIds++toDoIds // temporary update (*)
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
              i+1, j, unif0) // Move on to next parameter
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
  def combine(v1: Concretization, v2: ComponentView) : CombineResult = {
    combineCount += 1
    // println(s"combine($v1, $v2)")
    val servers = v1.servers; require(v2.servers == servers)
    val components1 = v1.components; val components2 = v2.components
    // View.checkDistinct(components2)
    // The initial maps: map0 is the identity on the server parameters;
    // otherArgs gives parameters used in v1 but not the servers; nextArg
    // gives the next fresh parameters.
    val (map0, otherArgs, nextArg) =  v1.getCombiningMaps

    if(debugging){      // IMPROVE: following checks are expensive
      var f = 0
      while(f < numTypes){
        // Check otherArgs(f) disjoint from ran(map0(f))
        var oa = otherArgs(f)
        while(oa.nonEmpty){
          require(!map0(f).contains(oa.head),
            s"combine1: otherArgs not disjoint from map0 for $f: "+
              map0(f).mkString("[",",","]")+"; "+
              otherArgs(f).mkString("[",",","]"))
          oa = oa.tail
        }
        // Check nextArg(f) holds next fresh value
        require(nextArg(f) > (
          if(otherArgs(f).isEmpty) map0(f).max
          else(map0(f).max max otherArgs(f).max)  ),
          s"combine1: nextArg($f) with incorrect value: "+nextArg(f)+"; "+
            map0(f).mkString("[",",","]")+"; "+
            otherArgs(f).mkString("[",",","]"))
        f += 1
      }
    } // end of if(debugging)

    combine1(map0, nextArg, otherArgs, components1, components2)
  }

  /** Try to combine two component views.  Produce all pi(v2), for remapping pi,
    * such that v1 U pi(v2) makes sense, i.e. agree on common components, and
    * a component of v2 unifies with some component of v1 such that the
    * corresponding entry in flags is true.  If the jth identity parameter of
    * v2 maps to the kth identity parameter of v1, then the corresponding
    * States much match.  Also return the index of the component of v2 that
    * the principal of v1 maps onto, if any, otherwise -1. */
  def combineWithUnification(
    v1: Concretization, flags: Array[Boolean], v2: ComponentView)
      : CombineResult = {
    Profiler.count("combineWithUnification")
    val servers = v1.servers; require(v2.servers == servers)
    val components1 = v1.components; val components2 = v2.components
    // View.checkDistinct(components2); 
    require(components1.length == flags.length)
    val result = new CombineResult 
    val (map0, otherArgs0, nextArg0) = v1.getCombiningMapsImmutable
    val otherArgs1 = new Array[List[Identity]](numTypes)
    val nextArg1 = new Array[Int](numTypes)

    var i = 0
    while(i < components1.length){
      if(flags(i)){
        val st1 = components1(i); var j = 0
        // Try to unify st1 with a state of v2
        while(j < components2.length){
          val st2 = components2(j)
          if(st1.cs == st2.cs){
            val map1 = unify(map0, st1, st2)
            if(map1 != null){
              //  make otherArgs1 and nextArg1 consistent with map1
              var f = 0
              while(f < numTypes){
                var xs = otherArgs0(f); var ys = List[Identity]()
                while(xs.nonEmpty){
                  val id = xs.head; xs = xs.tail; 
                  // Test if map1(f) contains id
                  var i = 0; val len = map1(f).length
                  while(i < len && map1(f)(i) != id) i += 1
                  if(i == len) ys = id::ys
                }
                otherArgs1(f) = ys
                nextArg1(f) = nextArg0(f) max (map1(f).max+1)
                f += 1
              }
              // IMPROVE:  don't remap st1?
              Profiler.count("combine2 with unification")
              combine2(map1, nextArg1, otherArgs1, components1, components2, 
                result, 0, 0, -1)
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
