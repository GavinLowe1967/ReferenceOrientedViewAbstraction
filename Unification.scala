package ViewAbstraction.RemapperP

import ViewAbstraction._
import ViewAbstraction.RemapperP._

import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet}

/** Operations concerned with unifying states or views. */
object Unification{

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
  private type UnificationList = List[(Int,Int)]

  type AllUnifsResult =  ArrayBuffer[(RemappingMap, UnificationList)]

  private def show(allUs: AllUnifsResult) = 
    allUs.map{case(map,us) => "("+Remapper.show(map)+", "+us+")"}.mkString("; ")

  /** All ways of extending map0 to unify elements of cpts with elements of
    * preCpts, other than the two principal components.  
    * 
    * For each combination of unifications, map0 is extended to a mapping map
    * so that if c = cpts(j) is unified with preC = preCpts(i), them map0(c) =
    * preC, and (j,i) is included in the UnificationList.  */
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
  private type BitMap = Array[Array[Boolean]]

  /** Result returned from combine(pre,...,cv).  Each entry represents a way of
    * remapping cv, paired with a UnificationList that contains (j,i) whenever
    * cv.components(j) unifies with pre.components(i). */
  type CombineResult = ArrayBuffer[(Array[State], UnificationList)]

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
  private def combine1(
    map: RemappingMap, otherArgs: OtherArgMap, bitMap: BitMap, 
    nextArg: NextArgMap, unifs: UnificationList, 
    cpts: Array[State], result: CombineResult)
      : Unit = {
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
    * post.servers, for which there has been a call to combine giving a
    * result with no unifications.  Note that we don't need to record
    * pre.servers explicitly, because it equals cv.servers. */ 
  private[RemapperP] val effectOnChangedServersCache = 
    new BasicHashSet[(ComponentView, ServerStates)] 
// FIXME: remove
  // private[RemapperP] val effectOnChangedServersCacheXXX = 
  //   new BasicHashSet[(ComponentView, ServerStates)]

  /** Reset effectOnChangedServersCache.  Necessary when performing multiple
    * checks. */
  def reset = effectOnChangedServersCache.clear

  // def eOCSCContains(cv: ComponentView, postServers: ServerStates) = 
  //   effectOnChangedServersCache.contains((cv, postServers))


  /** All ways of unifying pre and cv.  
    * 
    * Each parameter of cv is remapped (1) as identity function for parameters
    * in pre.servers; (2) if a unification of components is done, as required
    * by that unification; (3) otherwise either (a) to a parameter in
    * post.servers or the post-state of a unified component or the post state
    * of a component to which cv.principal gains a reference, or (b) for the
    * identity of the principal, an element of princRenames (when singleRef),
    * or (c) the next fresh variable.  In each case, the remapping is
    * restricted to be injective.  Also, under (a), identities cannot be
    * mapped to identities in post.components, other than with unification.
    * The choice under 3(a) is precisely those variables that will exist in
    * the post-state of cv (and are distinct post symmetry reduction).  
    * 
    * We suppress values that won't give a new view in effectOn.   
    * 
    * @return remapped state, paired with a UnificationList that contains
    * (j,i) whenever cv.components(j) unifies with pre.components(i).  */

// IMPROVE comment: at present, if singleRef also remaps to all params in
// pre.components.

  def combine(pre: Concretization, post: Concretization, cv: ComponentView,
    princRenames: List[Identity])
      : CombineResult = {
    // IMPROVE: some of the initial calculations depends only on pre and post, so
    // could be stored with the transition.
    require(singleRef || princRenames.isEmpty)
    // Profiler.count("princRenames"+princRenames.length) // norm 0, sometimes 1
    if(false) println(s"combine($pre, $post,\n  $cv, $princRenames)")
    val servers = pre.servers; require(servers == cv.servers)
    val preCpts = pre.components; val postCpts = post.components
    require(pre.components.length == postCpts.length)
    val changedServers = servers != post.servers
    val (cvpf, cvpid) = cv.principal.componentProcessIdentity
    val map0 = servers.remappingMap
    // Create NextArgMap, greater than anything in pre or post
    val nextArg: NextArgMap = pre.getNextArgMap; post.updateNextArgMap(nextArg)
    // All params in post.servers but not in pre.servers, as a bitmap.
    val newServerIds: Array[Array[Boolean]] = 
      ServerStates.newParamsBitMap(servers, post.servers)
// IMPROVE: following slows down lockFreeQueue a lot -- increases # return
// values by factor of 3.  I think this is necessary only when there's a cross
// reference (?).
// FIXME: I think it should be postCpts.
    if(singleRef)     // Add params of pre.cpts that are not in servers
      for(cpt <- preCpts) cpt.addIdsToBitMap(newServerIds, servers.numParams)
    // Bit map indicating which components have changed state.
    val changedStateBitMap = getChangedStateBitMap(preCpts, postCpts)
    val result = new CombineResult

    // Get all ways of unifying pre and cv. 
    val allUs = allUnifs(map0, pre.components, cv.components)

    /* Extend map1 with unifications unifs, adding all results to result. */
    def extendUnif(map1: RemappingMap, unifs: UnificationList) = {
      if(debugging) assert(Remapper.isInjective(map1), Remapper.show(map1))
      // Create OtherArgMap containing all values not in ran map1 or
      // pre.servers, but (1) in post.servers; or (2) in post.cpts for a
      // unified component or a component to which cv.principal gains a
      // reference.  newServerIds satisfies (1).
      val otherArgsBitMap = newServerIds.map(_.clone); var us = unifs
      // Add parameters of post.components corresponding to unifs, not shared
      // with servers.
      while(us.nonEmpty){
        val (j, i) = us.head; us = us.tail
        postCpts(i).addIdsToBitMap(otherArgsBitMap, servers.numParams)
        // If this is the unification of the principal of cv, which changes
        // state and gains a reference to another component c, include the
        // parameters of c from postCpts.
        if(!singleRef && j == 0 && preCpts(i) != postCpts(i))
          addIdsFromNewRef(
            otherArgsBitMap, servers.numParams, preCpts, postCpts, i)
// IMPROVE: think about the case with singleRef
      }
      // Remove values in ran map1
      Remapper.removeFromBitMap(map1, otherArgsBitMap)
      // Convert to OtherArgMap
      val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
      // Values that identities can be mapped to: values in otherArgs, but not
      // identities of components in post; update otherArgsBitMap to record.
      StateArray.removeIdsFromBitMap(postCpts, otherArgsBitMap)
      combine1(map1, otherArgs, otherArgsBitMap, nextArg, unifs,
        cv.components, result)
    } // end of extendUnif

    var ix = 0
    while(ix < allUs.length){
      val (map1, unifs) = allUs(ix); ix += 1
      // Does this create a cross reference from a secondary component to the
      // principal of cv (with singleRef).
      val acquiredCrossRef = princRenames.contains(map1(cvpf)(cvpid))
      // Do we need to consider this combination?  Either (1) the servers
      // changed, and either (a) we have some unification, or (b) this is the
      // first time for no unification with this combination of cv,
      // pre.servers and post.servers; or (2) the servers are unchanged but we
      // unify with a component that does change state.
      val sufficientUnif = isSufficientUnif(changedServers, unifs, post.servers,
        cv, changedStateBitMap, acquiredCrossRef) // || changedServers && princRenames.nonEmpty
      if(sufficientUnif){
        extendUnif(map1, unifs)
        // val inCache = effectOnChangedServersCacheXXX.contains((cv, post.servers))
        // if(! isSufficientUnifXXX(changedServers, unifs, post.servers,
        //   cv, changedStateBitMap, acquiredCrossRef))
        //   println(s"$pre -> $post;\n$cv; $unifs; $inCache")
      }
      // Try renaming cv.principal to each id in princRenames
      if(map1(cvpf)(cvpid) < 0) 
        for(newPId <- princRenames; if !map1(cvpf).contains(newPId)){
          assert(singleRef)
          map1(cvpf)(cvpid) = newPId; extendUnif(map1, unifs)
      }
    } // end of while loop

    result
  }
// IMPROVE: do we need all of unifs?
// IMPROVE, try to identify second case for sufficientUnifs within allUnifs,
// by trying to unify components that change state first.
// IMPROVE: can we share work between the calls to extendUnif? 

  /** Test if the current combination in combine needs to be considered.  Either
    * (1) the servers changed, and either (a) we have some unification, or (b)
    * this is the first time for no unification with this combination of cv,
    * pre.servers and post.servers; or (2) the servers are unchanged but we
    * unify with a component that does change state. 
    *  **** Different for singleRef
    * @param changedServers did the servers change state?
    * @paral unifs the list of unifications made.
    * @param postServers the post-state of the servers.
    * @param cv the view with which we're unifying.
    * @param changedStateBitMap a bitmap showing which components changed state 
    * in the transition. 
    * @param acquiredCrossRef with singleRef, has a secondary component acquired 
    * a reference to the principal of cv? */
  @inline private def isSufficientUnif(
    changedServers: Boolean, unifs: UnificationList, postServers: ServerStates, 
    cv: ComponentView, changedStateBitMap: Array[Boolean], 
    acquiredCrossRef: Boolean)
      : Boolean = {
    // Is there a unification with a component that changes state?
    @inline def changingUnif = {
      var us = unifs; var sufficientUnif = false
      while(!sufficientUnif && us.nonEmpty){
        sufficientUnif = changedStateBitMap(us.head._2); us = us.tail
      }
      sufficientUnif
    }

    if(singleRef){
      if(acquiredCrossRef) true
// IMPROVE:  case below?
      else if(changedServers) true
        // Following misses some views with lockFreeQueue
        // unifs.nonEmpty || effectOnChangedServersCache.add((cv, postServers))
      else // Is there a unification with a component that changes state?
        changingUnif
    } // end of if(singleRef)
    else if(changedServers)
      unifs.nonEmpty || effectOnChangedServersCache.add((cv, postServers))
      // Note, this can't be strengthened to
      // changingUnif || effectOnChangedServersCache.add((cv, postServers))
      // If there are two different ways of performing unification with a 
      // component that doesn't change state, this will find just one of them.
    else // Is there a unification with a component that changes state?
      changingUnif
  }

  // // Alternative, incorrect version -- don't see why.  FIXME: remove
  // @inline private def isSufficientUnifXXX(
  //   changedServers: Boolean, unifs: UnificationList, postServers: ServerStates, 
  //   cv: ComponentView, changedStateBitMap: Array[Boolean], 
  //   acquiredCrossRef: Boolean)
  //     : Boolean = {
  //   // Is there a unification with a component that changes state?
  //   def changingUnif = {
  //     var us = unifs; var sufficientUnif = false
  //     while(!sufficientUnif && us.nonEmpty){
  //       sufficientUnif = changedStateBitMap(us.head._2); us = us.tail
  //     }
  //     sufficientUnif
  //   }
  //   assert(!singleRef)
  //   if(changedServers)
  //     changingUnif || effectOnChangedServersCacheXXX.add((cv, postServers))
  //   else // Is there a unification with a component that changes state?
  //     changingUnif
  // }


  /** Bitmap showing which components changed state between preCpts and
    * postCpts. */
  @inline private 
  def getChangedStateBitMap(preCpts: Array[State], postCpts: Array[State])
      : Array[Boolean] = {
    val changedStateBitMap = new Array[Boolean](preCpts.length); var i = 0
    while(i < preCpts.length){
      changedStateBitMap(i) = preCpts(i) != postCpts(i); i += 1
    }
    changedStateBitMap
  }

  /** Add to otherArgsBitMap any parameters of a component c to which preCpts(i)
    * gains a reference as the result of the transition. */ 
  @inline private def addIdsFromNewRef(
    otherArgsBitMap: Array[Array[Boolean]], serverNumParams: Array[Int],
    preCpts: Array[State], postCpts: Array[State], i: Int) = {
// IMPROVE: think about the case with singleRef
    val prePids = preCpts(i).processIdentities
    val postPids = postCpts(i).processIdentities
    // Find which parameters are gained
    for(k <- 1 until postPids.length){
      val pid = postPids(k)
      if(!isDistinguished(pid._2) && !prePids.contains(pid)){
        // println(s"gains access to $pid")
        val c = StateArray.find(pid, postCpts)
        // I think assumptions imply pid must be in postCpts
        assert(c != null) // , s"\npre = $pre,\npost = $post,\ncv = $cv")
        // println(s"gains access to $c")
        c.addIdsToBitMap(otherArgsBitMap, serverNumParams)
      }
    }
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
    // We look to use combine1, although some of the parameters there aren't
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
      if(!isDistinguished(id) && map0(f)(id) < 0){
        otherArgs(f) ::= id; nextArgMap(f) = nextArgMap(f) max (id+1)
      }
    // println(s"otherArgs = "+otherArgs.mkString(", "))
    val result = new CombineResult
    // the bitmap is empty: c's id should not be remapped, by precondition.
    combine1(map0, otherArgs, newBitMap, nextArgMap, 
      List[(Int,Int)](), Array(c), result)
    result.map{ case(cs, _) => cs(0) }

  }


}
