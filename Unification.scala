package ViewAbstraction.RemapperP

import ViewAbstraction._
import ViewAbstraction.RemapperP._

import scala.collection.mutable.ArrayBuffer

/** Operations concerned with unifying states or views. */
object Unification{
  import Remapper.{RemappingMap,NextArgMap}

  var combineCount = 0L
  var renameXCount = 0L
  var combineRecCount = 0L
  var combine1Count = 0L

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
  //private[RemapperP] 
  def combine1(map0: RemappingMap, nextArg: NextArgMap,
    otherArgs: Array[List[Identity]], cpts1: Array[State], cpts2: Array[State]) 
      : ArrayBuffer[(Array[State], Unifications)] = {
    combine1Count += 1
    // Profiler.count("combine1")
    var f = 0
    // IMPROVE: following checks are expensive
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
    // Check elements of cpts1 are distinct
    // for(i <- 0 until cpts1.length; j <- i+1 until cpts1.length)
    //   assert(cpts1(i) != cpts1(j), View.showStates(cpts1))
    // println("combine1: "+showRemappingMap(map0)+"; "+
    //   nextArg.mkString("[",",","]")+"; "+otherArgs.mkString("[",",","]")+"; "+
    //   cpts1.mkString("[",",","]")+"; "+cpts2.mkString("[",",","]"))
    val result = new ArrayBuffer[(Array[State], Unifications)]

    // Extend map to remap cpts2(j).ids[i..) and then cpts2[j+1..). 
    def combineRec(map: RemappingMap, i: Int, j: Int, unifs: Unifications)
        : Unit = {
      combineRecCount += 1
      // Profiler.count("combineRec")
      // for(f <- 0 until numTypes) // IMPROVE
      //   require(otherArgs(f).forall(id => !map(f).contains(id)),
      //     s"combineRec: otherArgs not disjoint from map for $f: "+
      //  map(f).mkString("[",",","]")+"; "+otherArgs(f).mkString("[",",","]"))
      //require(isInjective(map), "combineRec: "+showRemappingMap(map))//IMPROVE
      // println(s"combineRec(${showRemappingMap(map)}, $i, $j)")
      if(j == cpts2.length) 
        result += ((Remapper.applyRemapping(map, cpts2), unifs))  // base case
      else{
        val c = cpts2(j); val ids = c.ids; val typeMap = c.typeMap
        if(i == ids.length) // End of this component
          combineRec(map, 0, j+1, unifs) // move on to the next component
        else{
          val id = ids(i); val f = typeMap(i)
          if(isDistinguished(id)) combineRec(map, i+1, j, unifs) // just move on
          else{ // rename (f, id)
            // Case 1: map id to the corresponding value idX in map, if any;
            // otherwise to an element id1 of otherArgs(f).
            val idX = map(f)(id) 
            // Rename id to id1
            def renameX(id1: Identity) = {
              // Profiler.count("renameX"); 
              renameXCount += 1
              if(i == 0){ // Identity; see if any cpt of cpts1 matches (f, id1)
                var matchedId = false // have we found a cpt with matching id?
                var k = 0
                while(k < cpts1.length){
                  val c1 = cpts1(k)
                  if(c1.componentProcessIdentity == (f,id1)){
                    // val map1 = extendMap(map, f, id, id1)
                    assert(!matchedId, View.showStates(cpts1)+": "+(f,id1))
                    matchedId = true
                    // val map1 = extendMap(map, f, id, id1)
                    map(f)(id) = id1 // temporary update (*)
                    val map2 = unify(map, c1, c)
                    if(map2 != null){
                      // Update otherArgs to be disjoint from ran map2.
                      val oldOtherArgs = otherArgs.clone; var f1 = 0
                      while(f1 < numTypes){
                        // @noinline def XX = {
                        otherArgs(f1) = 
                          otherArgs(f1).filter(id => !map2(f1).contains(id)) // }
                        // XX
                        f1 += 1
                      }
                      combineRec(map2, 0, j+1, (k,j)::unifs)
                      // Undo previous update
                      f1 = 0
                      while(f1 < numTypes){
                        otherArgs(f1) = oldOtherArgs(f1); f1 += 1
                      }
                    }
                    map(f)(id) = idX // backtrack (*)
                  }
                  k += 1
                } // end of while(k < ...)
                if(!matchedId){ // No cpt of cpts1 matched; move on   
                  map(f)(id) = id1 // temporary update (*)
                  combineRec(map, i+1, j, unifs) 
                  map(f)(id) = idX // backtrack (*)
                }
              } // end of if(i == 0)
              else{  // Move on to next parameter
                map(f)(id) = id1  // temporary update (*)
                combineRec(map, i+1, j, unifs)
                map(f)(id) = idX // backtrack (*)
              }
            } // end of renameX

            if(idX < 0){
              // Call renameX for each id1 in otherArgs(f), with id1 removed
              // from otherArgs(f).  toDoIds represents the identities still
              // to deal with; doneIds is those already done.
              var toDoIds = otherArgs(f); var doneIds = List[Identity]()
              // Profiler.count("combineRec"+toDoIds.length)
              // 0: 5%; 1: 60%; 2: 30%; 3: 5%
              while(toDoIds.nonEmpty){
                val id1 = toDoIds.head; toDoIds = toDoIds.tail
                otherArgs(f) = doneIds++toDoIds // temporary update (*)
                renameX(id1)
                doneIds = id1::doneIds // doneIds:+id1 -- order doesn't matter
              }
              otherArgs(f) = doneIds // undo (*)
            }
            else{ 
              // assert(!otherArgs(f).contains(idX), 
              //   show(map)+"; "+f+"; "+otherArgs(f))
              renameX(idX) 
            }

            // Case 2: map id to nextArg(f)
            if(idX < 0){ 
              val id1 = nextArg(f); nextArg(f) += 1 // temporary update (+)
              map(f)(id) = id1 // (+)  // val map1 = extendMap(map, f, id, id1) 
              combineRec(map, i+1, j, unifs) // Move on to next parameter
              nextArg(f) -= 1; map(f)(id) = idX  // undo (+)
            }
          }
        }
      }
    } // end of combineRec

    combineRec(map0, 0, 0, List()); result
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
    View.checkDistinct(components2)
    // The initial maps: map0 is the identity on the server parameters;
    // otherArgs gives parameters used in v1 but not the servers; nextArg
    // gives the next fresh parameters.
    val (map0, otherArgs, nextArg) = 
      Remapper.createCombiningMaps(servers, components1)
    // IMPROVE: inline combine1
    combine1(map0, nextArg, otherArgs, components1, components2)
  }


}
