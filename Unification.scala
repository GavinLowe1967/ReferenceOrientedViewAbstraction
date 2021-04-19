package ViewAbstraction.RemapperP

import ViewAbstraction._
import ViewAbstraction.RemapperP._

import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet}

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
      val k = if(i > 0) -1 else View.findIndex(cpts1, f, id1)
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
              otherArgs(f) = append1(doneIds, toDoIds) // temporary update (*)
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
  def combineXXX(v1: Concretization, v2: ComponentView) : CombineResult = {
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

  private type UnificationList = List[(Int,Int)]

  type AllUnifsResult =  ArrayBuffer[(RemappingMap, UnificationList)]

  /** All ways of extending map0 to a mapping map so that for each component c =
    * cpts(j) whose identity is in dom map, map(c) agrees with any component
    * preC = preCpts(i) with the same identity.  Also include the pair (j,i)
    * in the UnificationList.  */
  private[RemapperP] def allUnifs(
    map0: RemappingMap, preCpts: Array[State], cpts: Array[State]) 
      : AllUnifsResult = {
    // Map from identities to the index of the corresponding component in
    // preCpts, if any, otherwise -1.
    val preCptsIndexMap = State.indexMap(preCpts)
    val result = new AllUnifsResult // holds final result

    // Extend map and unifs to cpts[from..), adding results to results. 
    def allUnifsRec(map: RemappingMap, from: Int, unifs: UnificationList)
        : Unit = {
      // println(s"$from: "+Remapper.show(map)+"; "+unifs)
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
        val ix = 
          if(id1 < 0) -1 
          else{ 
            assert(id1 < preCptsIndexMap(fc).length, 
              s"preCpts = ${View.showStates(preCpts)} "+
                s"cpts = ${View.showStates(cpts)} id1 = $id1")
            preCptsIndexMap(fc)(id1)
          }
        if(ix >= 0) tryUnify(ix) 
        else{
          // Try to unify with each component in turn, but don't unify the two
          // principals (that would just recreate the same transition).
          var i = if(from == 0) 1 else 0
          while(i < preCpts.length){ tryUnify(i); i += 1 }
          // No unifications for c
          allUnifsRec(map, from+1, unifs)
        }
      }
    } // end of allUnifsRec

    allUnifsRec(map0, 0, List())
    result
  }

  private type BitMap = Array[Array[Boolean]]

  type NewCombineResult = ArrayBuffer[(Array[State], UnificationList)]

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
  private def combineX(
    map: RemappingMap, otherArgs: OtherArgMap, bitMap: BitMap, 
    nextArg: NextArgMap, unifs: UnificationList, 
    cpts: Array[State], result: NewCombineResult)
      : Unit = {
    // println(s"combineX: $unifs")

    // Recursively remap cpts(i).args[j..), then cpts[i+1..).
    def rec(i: Int, j: Int): Unit = {
      if(i == cpts.length){
        // println((View.showStates(Remapper.applyRemapping(map, cpts)), unifs))
        // IMPROVE: remap each state in turn (and clone at this point)
        result += ((Remapper.applyRemapping(map, cpts), unifs))
      }
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
            // val isIdentity = cpts.exists(st => st.family == f && st.id == id)
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


  /** Record of the cv, pre.servers and post.servers, with pre.servers !=
    *  post.servers, for which there has been a call to newCombine giving a
    *  result with no unifications.  Note that we don't need to record
    *  pre.servers explicitly, because it equals cv.servers. */ 
  private[RemapperP] val effectOnChangedServersCache = 
    new BasicHashSet[(ComponentView, /* ServerStates,*/ ServerStates)]

  /** All ways of unifying pre and cv.  Each parameter of cv is remapped (1) as
    * identity function for parameters in pre.servers; (2) if a unification is
    * done, as required by that unification; (3) otherwise either (a) to a
    * parameter in post.servers or the post-state of a unified component, but
    * not in pre.servers, or (b) the next fresh variable.  Also, under (a),
    * identities cannot be mapped to identities in post.components, other than
    * with unification.  Return remapped state, paired with a
    * ReunificationList such that contains (j,i) whenever cv.components(j)
    * unifies with pre.components(i).  */
  def newCombine(pre: Concretization, post: Concretization, cv: ComponentView) 
      : NewCombineResult = {
    val servers = pre.servers; require(servers == cv.servers)
    val preCpts = pre.components; val postCpts = post.components
    require(pre.components.length == postCpts.length)
    val changedServers = servers != post.servers
    val map0 = servers.remappingMap
    // Create NextArgMap, greater than anything in pre or post
    val nextArg: NextArgMap = pre.getNextArgMap; post.updateNextArgMap(nextArg)
    // Find all ids in post.servers but not in pre.servers, as a bitmap.
    val newServerIds = new Array[Array[Boolean]](numTypes); var f = 0
    while(f < numTypes){ 
      newServerIds(f) = new Array[Boolean](typeSizes(f)); f += 1
// Is above size enough?
    }
    var sts: List[State] = post.servers.servers
    while(sts.nonEmpty){
      val pids = sts.head.processIdentities; sts = sts.tail; var i = 0
      while(i < pids.length){
        val (f,id) = pids(i); i += 1
        if(id >= servers.numParams(f)) newServerIds(f)(id) = true
      }
    }
    // Bit map indicating which components have changed state.
    val changedStateBitMap = new Array[Boolean](preCpts.length); var i = 0
    while(i < preCpts.length){
      changedStateBitMap(i) = preCpts(i) != postCpts(i); i += 1
    }
    val result = new NewCombineResult

    // Get all ways of unifying pre and cv. 
    val allUs = allUnifs(map0, pre.components, cv.components)
    var ix = 0
    while(ix < allUs.length){
      val (map1, unifs) = allUs(ix); ix += 1
      // Test if either (1) the servers changed, and either (a) we have some
      // unification, or (b) this is the first time for no unification with
      // this combination of cv, pre.servers and post.servers; or (2) the
      // servers are unchanged but we unify with a component that does change
      // state.  If not, we can ignore this combination.
      var sufficientUnif = false
      if(changedServers)
        sufficientUnif = unifs.nonEmpty ||
          effectOnChangedServersCache.add((cv, /* pre.servers,*/ post.servers))
      else{
        var us = unifs
        while(!sufficientUnif && us.nonEmpty){
          sufficientUnif = changedStateBitMap(us.head._2); us = us.tail
        }
// IMPROVE, try to identify this within allUnifs, by trying to unify
// components that change state first.
      }
      // Profiler.count(s"sufficientUnif = $sufficientUnif$changedServers${unifs.nonEmpty}")
      if(sufficientUnif){
        //if(changedServers && unifs.isEmpty)  Profiler.count(cv.toString+post.servers)
        // println("newCombine: "+Remapper.show(map1)+"; "+unifs)
        // Create OtherArgMap containing all values not in ran map1 or
        // pre.servers, but (1) in post.servers; or (2) in post.cpts for a
        // unified component.  Start with a bit map.
        val otherArgsBitMap = newServerIds.map(_.clone)
        // Add values in components of post corresponding to unifs.
        var us = unifs
        while(us.nonEmpty){
          val i = us.head._2; us = us.tail
          val pids = postCpts(i).processIdentities; var j = 0
          // Add values in pids to otherArgsBitMap
          while(j < pids.length){
            val (f,id) = pids(j); j += 1
            assert(id < otherArgsBitMap(f).length, 
              s"pre = ${pre.toString0}, post = ${post.toString0}, "+
                s"cv = ${cv.toString0}, id = $id")
// FIXME: throw better exception here?
            if(id >= servers.numParams(f)) otherArgsBitMap(f)(id) = true
          }
        }
        // Remove values in ran map1, and convert into otherArgMap
        val otherArgs = Remapper.newOtherArgMap; var f = 0
        while(f < numFamilies){
          var i = 0; val len = typeSizes(f)
          while(i < len){
            val id = map1(f)(i); i += 1
            if(id >= 0) otherArgsBitMap(f)(id) = false
          }
          // Create otherArgs(f)
          i = 0
          while(i < len){
            if(otherArgsBitMap(f)(i)) otherArgs(f) ::= i
            i += 1
          }
          f += 1
        }
        // Find values that identities can be mapped to: values in otherArgs,
        // but not identities of components in post; update otherArgsBitMap to
        // record.
        var i = 0
        while(i < postCpts.length){
          val st = postCpts(i); i += 1; otherArgsBitMap(st.family)(st.id) = false
        }

        if(false){
          println("\nunifs = "+unifs)
          println("map1 = "+Remapper.show(map1))
          println("otherArgs = "+otherArgs.mkString(", "))
          println("nextArg = "+nextArg.mkString(", "))
          val otherIds = (0 until numTypes).map(f =>
            otherArgs(f).filter(id => otherArgsBitMap(f)(id)))
          println("otherIds = "+otherIds.mkString(", "))
        }
        // IMPROVE: inline?
        combineX(
          map1, otherArgs, otherArgsBitMap, nextArg, unifs, 
          cv.components, result)
// IMPROVE: do we need all of unifs? 

      } // end of if
    } // end of while loop

    result
  }

}
