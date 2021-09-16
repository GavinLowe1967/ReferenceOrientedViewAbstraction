package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper

import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet}

/** Operations concerned with unifying states or views. */
object Unification{
  /* Relationship of main functions:
   * 
   * combine
   * |--allUnifs
   * |  |--unify
   * |--extendUnif
   * |  |--extendUnifSingleRef
   * |  |  |--remapToCreateSingleRefs
   * |  |  |--combine1
   * |  |--combine1
   * |--isSufficientUnif
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
  private def allUnifs(
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
  // private val effectOnChangedServersCache = 
  //   new BasicHashSet[(ComponentView, ServerStates)] 

  /** Reset effectOnChangedServersCache.  Necessary when performing multiple
    * checks. */
  def reset = { } // effectOnChangedServersCache.clear

  /** The part of the result corresponding to secondary induced transitions.
    * The Int field is the index of the component in pre/post that gains
    * access to cv.principal. */
  type CombineResult2 = ArrayBuffer[(Array[State], UnificationList, Int)]

  /** All ways of unifying pre and cv.  
    * 
    * Each parameter of cv is remapped (1) as identity function for parameters
    * in pre.servers; (2) if a unification of components is done, as required
    * by that unification; (3) otherwise either (a) to a parameter in
    * post.servers or the post-state of a unified component or the post state
    * of a component to which cv.principal gains a reference, or (b) the next
    * fresh value.  In each case, the remapping is restricted to be injective.
    * Also, under (a), identities cannot be mapped to identities in
    * post.components, other than with unification.  The choice under 3(a) is
    * precisely those variables that will exist in the post-state of cv (and
    * are distinct post symmetry reduction).  The first component of the
    * returned result contains each such remapped state, paired with a
    * UnificationList that contains (j,i) whenever cv.components(j) unifies
    * with pre.components(i).
    * 
    * The second component of the result contains information concerning
    * secondary induced transitions under singleRef.  In this case, c2Refs
    * contains pairs (i,id) such that post.components(i) gains a reference in
    * parameter id to a value of the same type as cv.principal.id.  For each
    * such (i,id), each parameter of cv is renamed as under (1) or (2) above;
    * or (3) cv.principal.id is renamed to id; (4) every other parameter of
    * cv.principal can be renamed to a parameter in post.servers or a
    * parameter of post.components(i) or the next fresh value.  Each element
    * of the second component of the result contains: the remapped state, the
    * unification list (as above), and the parameter i.
    * 
    * We suppress values that won't give a new view in effectOn.   
    * 
    * @return remapped state, paired with a UnificationList that contains
    * (j,i) whenever cv.components(j) unifies with pre.components(i).  */
  def combine(pre: Concretization, post: Concretization, cv: ComponentView,
    c2Refs : List[(Int,Identity)])
      : (CombineResult, CombineResult2) = {
    // IMPROVE: some of the initial calculations depends only on pre and post, so
    // could be stored with the transition.
    val princRenames = c2Refs.map(_._2) // normally empty; sometimes singleton
    require(singleRef || princRenames.isEmpty)
    // if(false) println(s"combine($pre, $post,\n  $cv, $princRenames)")
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
    // Bit map indicating which components have changed state.
    val changedStateBitMap = getChangedStateBitMap(preCpts, postCpts)
    val result = new CombineResult; val result2 = new CombineResult2
    // Extending a particular way of unifying pre and cv.
    val extendUnif1 = extendUnif(
      servers, preCpts, postCpts, cv,  c2Refs, newServerIds,
      nextArg, changedStateBitMap, result, result2) _ 

    // Get all ways of unifying pre and cv. 
    val allUs = allUnifs(map0, pre.components, cv.components)
    var ix = 0
    while(ix < allUs.length){
      val (map1, unifs) = allUs(ix); ix += 1
      // Does this create a cross reference from a secondary component to the
      // principal of cv (with singleRef)?
      val acquiredCrossRef = princRenames.contains(map1(cvpf)(cvpid))
      // Do we need to consider this combination?  Either (1) the servers
      // changed, and either (a) we have some unification, or (b) this is the
      // first time for no unification with this combination of cv,
      // pre.servers and post.servers; or (2) the servers are unchanged but we
      // unify with a component that does change state.
      val sufficientUnif = isSufficientUnif(changedServers, unifs, post.servers,
        cv, changedStateBitMap, acquiredCrossRef)
      // if(singleRef && !acquiredCrossRef && changedServers && unifs.isEmpty && 
      //   cv.doneInducedContains(post.servers))
      //   println(s"Considering $pre -> $post  on $cv")
      if(c2Refs.nonEmpty || sufficientUnif) 
        extendUnif1(map1, unifs, sufficientUnif)
    } // end of while loop

    (result, result2)
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
      if(unifs.length == cv.components.length && unifs.contains((0,0))){
        /*println(s"Avoiding unification with $unifs");*/ false
      }
      else if(acquiredCrossRef) true
// IMPROVE:  case below?
      else if(changedServers){
        // if(unifs.isEmpty && cv.doneInducedContains(postServers))
        //   println(s"Considering induced on $cv with $postServers")
        true   
        // I don't know why the following doesn't work.  Maybe the add in
        // EffectOn.processInducedInfo should check !acquiredCrossRef
        // unifs.nonEmpty || !cv.doneInducedContains(postServers)
      }
        // Following misses some views with lockFreeQueue
        // unifs.nonEmpty || effectOnChangedServersCache.add((cv, postServers))
      else // Is there a unification with a component that changes state?
        changingUnif
    } // end of if(singleRef)
    else if(changedServers)
      unifs.nonEmpty || cv.addDoneInduced(postServers) // effectOnChangedServersCache.add((cv, postServers))
      // Note, this can't be strengthened to
      // changingUnif || effectOnChangedServersCache.add((cv, postServers))
      // If there are two different ways of performing unification with a 
      // component that doesn't change state, this will find just one of them.
    else // Is there a unification with a component that changes state?
      changingUnif
  }

  /** Extend map1 with unifications unifs, corresponding to transitions induced
    * by the transition pre -> post (with pre = (servers, preCpts)) on cv.
    * 
    * If sufficientUnif, create representatives of all remappings of cv to be
    * accordant with pre, and add to result.  Also create renamings
    * corresponding to secondary induced transitions, and add results to
    * result2.
    * 
    * Parameters must be remapped consistent with map1.  Parameters undefined
    * in map1 can be mapped: (1) to a parameter in newServerIds; (2) a
    * parameter of postCpts corresponding to a unification; (3) if the
    * principal of cv is unified with a component that changes state and gains
    * a reference to a component c, then the parameters of c; (4) a fresh
    * value, given by nextArg.  
// Also all params of pre.cpts if singleRef ************ 
    * Proviso: identities cannot be mapped to
    * identities in preCpts.  Each remapped state and corresponding
    * unifications is added to result.
    * 
    * In addition, with singleRef, result2 contains information about
    * secondary induced transitions.  For each (k,p) in c2Refs:
    * cv.principal.id gets mapped to p; and every other parameter gets mapped
    * as in (1) or (4), or (5) to a parameter of post.components(k). Each
    * remapped state, corresponding unifications and parameter k is added to
    * result.
    * 
    * This function would live more happily inside combine; but that function
    * is just too large.  All other parameters are as there. 
    * 
    * @param unifs a representation of unifications between cv and pre.  
    * @param map1 the mapping corresponding to unifs. 
    * @param c2Refs if singleRef, pairs (k,p) such that the kth secondary
    * component might obtain a reference to cv.princ in its parameter p.
    * @param newServerIds bit map giving parameters in pre.servers but not 
    * post.servers.
    * @param nextArg a NextArgMap giving the next fresh value to use.
    * @param changedStateBitMap a bit map showing which components changed state
    * in the transition. */
  @inline private def extendUnif(
    servers: ServerStates, preCpts: Array[State], postCpts: Array[State], 
    cv: ComponentView, c2Refs: List[(Int,Identity)],
    newServerIds: Array[Array[Boolean]], nextArg: NextArgMap, 
    changedStateBitMap: Array[Boolean],
    result: CombineResult, result2: CombineResult2)
    (map1: RemappingMap, unifs: UnificationList, sufficientUnif: Boolean)
      : Unit = {
    if(debugging) assert(Remapper.isInjective(map1), Remapper.show(map1))
    // Create OtherArgMap containing all values not in ran map1 or
    // pre.servers, but (1) in post.servers; or (2) in post.cpts for a unified
    // component or a component to which cv.principal gains a reference.
    // newServerIds satisfies (1).
    val otherArgsBitMap = newServerIds.map(_.clone); var us = unifs
    // (2) Add parameters of post.components corresponding to unifs, not shared
    // with servers.
    while(us.nonEmpty){
      val (j, i) = us.head; us = us.tail
      postCpts(i).addIdsToBitMap(otherArgsBitMap, servers.numParams)
      // (3) If this is the unification of the principal of cv, which changes
      // state and gains a reference to another component c, include the
      // parameters of c from postCpts.
      if(j == 0 && changedStateBitMap(i)) addIdsFromNewRef(
        otherArgsBitMap, servers.numParams, preCpts, postCpts, i)
    }
    // If singleRef, add parameters of preCpts.
    if(singleRef) 
      extendUnifSingleRef(
        servers, preCpts, postCpts, cv, c2Refs, changedStateBitMap, 
        result, result2, map1, otherArgsBitMap, nextArg, unifs, sufficientUnif)
    else{
      // Remove values in ran map1
      Remapper.removeFromBitMap(map1, otherArgsBitMap)
      // Convert to OtherArgMap
      val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
      // Values that identities can be mapped to: values in otherArgs, but not
      // identities of components in post; update otherArgsBitMap to record.
      StateArray.removeIdsFromBitMap(postCpts, otherArgsBitMap)
      // Create primary induced transitions.
      assert(sufficientUnif)
      combine1(map1, otherArgs, otherArgsBitMap, nextArg, unifs,
        cv.components, result)
    }
  } // end of extendUnif


  /** Second part of extendUnif in the case of singleRef. 
    * Most parameters are as for extendUnif.
    * @param otherArgsBitMap a bit map giving values that parameters of cv could 
    * be mapped to, and satisfying cases (1)-(3) in the description of
    * extendUnif.
// IMPROVE: not all of these are needed for secondary induced transitions
    */
  @inline private def extendUnifSingleRef(
    servers: ServerStates, preCpts: Array[State], postCpts: Array[State], 
    cv: ComponentView, c2Refs: List[(Int,Identity)], 
    changedStateBitMap: Array[Boolean], 
    result: CombineResult, result2: CombineResult2,
    map0: RemappingMap, otherArgsBitMap0: Array[Array[Boolean]], 
    nextArg: NextArgMap, unifs: UnificationList, sufficientUnif: Boolean)
  = {
    require(singleRef)
    val (cvpf, cvpid) = cv.principal.componentProcessIdentity

    // Consider which identities of cpts are remapped to match a non-identity
    // of preCpts, or non-identities of cpts that are remapped to match an
    // identity of preCpts.
    val crossRefs = remapToCreateCrossRefs(preCpts, cv.components, map0)
    for((map1, tuples) <- crossRefs){
      // Clone, to avoid interference between different iterations. 
      val otherArgsBitMap = otherArgsBitMap0.map(_.clone)
      // Indices of components of preCpts that are mapped onto.
      val rangeIndices = tuples.map{ case ((i1,_),_) => i1 }.distinct
      for(i1 <- rangeIndices)
        preCpts(i1).addIdsToBitMap(otherArgsBitMap, servers.numParams)
      // IMPROVE: we need only map parameters of cpts(i2) like this, where
      // i2 is the relevant index in the current tuple.
      // for(cpt <- preCpts) cpt.addIdsToBitMap(otherArgsBitMap, servers.numParams)
      // Remove values in ran map1
      Remapper.removeFromBitMap(map1, otherArgsBitMap)
      // Convert to OtherArgMap
      val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
      // Values that identities can be mapped to: values in otherArgs, but not
      // identities of components in post; update otherArgsBitMap to record.
      StateArray.removeIdsFromBitMap(postCpts, otherArgsBitMap)
      // Create primary induced transitions.
      if(sufficientUnif)
        combine1(map1, otherArgs, otherArgsBitMap, nextArg, unifs,
          cv.components, result)

      /* Build remappings for secondary induced transitions corresponding to
       * component k acquiring a reference to cv.principal in parameter id. */
      @inline def mkSecondaryRemaps(k: Int, id: Int) = {
        require(map1(cvpf)(cvpid) == id)
        // (5) For each other parameter of postCpts(k), if not in ran map1, add
        // to otherArgs, and to otherArgsBitMap if not an identity in postCpts.
        for((t,id1) <- postCpts(k).processIdentities)
          if(id1 != id && !contains(map1(t),id1) && !contains(otherArgs(t),id1)){
            otherArgs(t) ::= id1
            if(StateArray.findIndex(postCpts, t, id1) < 0)
              otherArgsBitMap(t)(id1) = true
          }
        val tempRes = new CombineResult
        combine1(map1, otherArgs, otherArgsBitMap, nextArg, unifs,
          cv.components, tempRes)
        for((newSts, us) <- tempRes){ // IMPROVE
          assert(us eq unifs); result2 += ((newSts, us, k))
        }
      } // end of mkSecondaryRemaps

      for((k,p) <- c2Refs){
        assert(changedStateBitMap(k))
        if(map1(cvpf)(cvpid) == p) mkSecondaryRemaps(k, p)
        else if(map1(cvpf)(cvpid) < 0 && !contains(map1(cvpf), p)){
          // Consider mapping cvpid to p (and backtrack)
          map1(cvpf)(cvpid) = p; mkSecondaryRemaps(k, p); map1(cvpf)(cvpid) = -1
        }
      }
    } // end of outer for loop.
  } // end of extendUnifSingleRef


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
    val prePids = preCpts(i).processIdentities
    val postPids = postCpts(i).processIdentities
    // Find which parameters are gained
    for(k <- 1 until postPids.length){
      val pid = postPids(k)
      if(!isDistinguished(pid._2) && !prePids.contains(pid)){
        val c = StateArray.find(pid, postCpts)
        // Assumptions imply pid must be in postCpts, except under singleRef.
        if(c != null) c.addIdsToBitMap(otherArgsBitMap, serverNumParams)
        else assert(singleRef)
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

  /** A tuple in a remapping from cpts to preCpts.  Each tuple ((i1,j1),(i2,j2))
    * indicates that parameter j2 of cpts(i2) is mapped to match parameter j1
    * of preCpts(i1).  Precisely one of j1 and j2 equals 0. */
  type MatchingTuple = ((Int,Int), (Int, Int))

  /** All ways of extending map (over cpts) so that an identity in cpts matches
    * a non-identity parameter in preCpts, or a non-identity parameter in
    * preCpts matches an identity in cpts; but no identity should map to an
    * identity.
    * @return the resulting map, together with a list of tuples
    * ((i1,j1), (i2,j2)) indicating that parameter j2 of cpts(i2) is mapped to
    * match paramter j1 of preCpts(i1); precisely one of j1 and j2 will be 0. */
  private def remapToCreateCrossRefs(
    preCpts: Array[State], cpts: Array[State], map: RemappingMap)
      : ArrayBuffer[(RemappingMap, List[MatchingTuple])] = {
    // Identities of preCpts, cpts
    val preIds = Array.tabulate(preCpts.length)(
      i => preCpts(i).componentProcessIdentity)
    val ids = Array.tabulate(cpts.length)(i => cpts(i).componentProcessIdentity)
    // Bit map (indexed by component number, param number) showing which
    // parameters of preCpts can be mapped onto: all identities; and
    // non-identities those that are not distinguished, do not match any
    // identity in preCpts, and are the first instance in preCpts.
    val rangeBitMap = new Array[Array[Boolean]](preCpts.length)
    var seen = newBitMap // ids seen so far
    for(i <- 0 until preCpts.length){
      val cpt = preCpts(i); rangeBitMap(i) = new Array[Boolean](cpt.length)
      rangeBitMap(i)(0) = true
      for(j <- 1 until cpt.length){
        val (t,p) = cpt.processIdentity(j)
        if(!isDistinguished(p) && !seen(t)(p) && !preIds.contains((t,p))){
          rangeBitMap(i)(j) = true; seen(t)(p) = true
        }
      }
    }
    // Similar bit map for cpts, showing which non identity params can be
    // mapped.
    val domBitMap = new Array[Array[Boolean]](cpts.length); seen = newBitMap
    for(i <- 0 until cpts.length){
      val cpt = cpts(i); domBitMap(i) = new Array[Boolean](cpt.length)
      domBitMap(i)(0) = true
      for(j <- 1 until cpt.length){
        val (t,p) = cpt.processIdentity(j)
        if(!isDistinguished(p) && !seen(t)(p) && !ids.contains((t,p))){
          domBitMap(i)(j) = true; seen(t)(p) = true
        }
      }
    }
    val result = new ArrayBuffer[(RemappingMap, List[MatchingTuple])]

    // Next component of preCpts(i1) to try mapping on to.  The minimum j in
    // [j1, preCpts(i1).length) s.t. rangeBitMap(i1)(j); or preCpts(i1).length
    // if there is no such.
    @inline def advanceInPreCpts(i1: Int, j1: Int) = {
      var j = j1
      while(j < preCpts(i1).length && !rangeBitMap(i1)(j)) j += 1
      j
    }

    /* Consider extending map and tuples so as to map parameter j2 of cpts(i2) to
     * match parameter j1 of preCpts(i1); then continue, considering
     * parameters in lexicographic order.  All updates to map are backtracked.
     * Pre: (1) Exactly one of j1 and j2 is 0.  (2) rangeBitMap(i1)(j1), or one
     * of i1, j1 is out of range. */
    @inline def rec(tuples: List[MatchingTuple],
      i1: Int, j1: Int, i2: Int, j2: Int)
        : Unit = {
      // println(s"i1 = $i1, j1 = $j1; i2 = $i2, j2 = $j2")
      assert((j1 == 0) ^ (j2 == 0), s"j1 = $j1; j2 = $j2")
      assert(i1 == preCpts.length || j1 == preCpts(i1).length ||
        rangeBitMap(i1)(j1))
      if(i1 == preCpts.length)  // finished this branch
        result += ((Remapper.cloneMap(map), tuples))
      // Various cases of advancing
      else if(j1 == preCpts(i1).length) // Move to next cpt of preCpts
        rec(tuples, i1+1, 0, 0, 1)
      else if(i2 == cpts.length) 
        // At end of cpts; advance to next parameter in preCpts(i1) that can
        // be mapped to.
        rec(tuples, i1, advanceInPreCpts(i1,j1+1), 0, 0) 
      else if(j2 == cpts(i2).length) // advance to next component of cpts
        rec(tuples, i1, j1, i2+1, if(j1 == 0) 1 else 0)
      else{
        if(domBitMap(i2)(j2)){ // Improve: make this a precondition
          // Try to map id2 to match id1
          val id1 = preCpts(i1).ids(j1); val id2 = cpts(i2).ids(j2)
          val t = preCpts(i1).typeMap(j1)
          assert(!isDistinguished(id1) && !isDistinguished(id2), 
            StateArray.show(preCpts)+"\n"+StateArray.show(cpts)+"\n"+
              s"($i1,$j1), ($i2,$j2), ($t,$id1), ($t, $id2)")
          if(t == cpts(i2).typeMap(j2) && map(t)(id2) < 0 &&
              !map(t).contains(id1) ){ // IMPROVE
            assert((!preIds.contains((t,id1)) || !ids.contains((t,id2))),
              StateArray.show(preCpts)+"\n"+StateArray.show(cpts)+"\n"+
                s"($i1,$j1), ($i2,$j2), ($t,$id1), ($t, $id2)")
            map(t)(id2) = id1 // temporary update (*)
            val newTuples = ((i1,j1),(i2,j2))::tuples
            // Advance
            if(j1 == 0) rec(newTuples, i1, j1, i2, j2+1)
            else rec(newTuples, i1, j1, i2+1, 0)
            map(t)(id2) = -1 // backtrack (*)
          }
        }
        // Also just advance (whether or not we did the if)
        if(j1 == 0) rec(tuples, i1, j1, i2, j2+1)
        else rec(tuples, i1, j1, i2+1, 0)
      }
    } // end of rec

    val j1 =  advanceInPreCpts(0,0)
    rec(List[MatchingTuple](), 0, j1, 0, if(j1 == 0) 1 else 0)
    result
  }

  /** Hooks for testing. */
  trait Tester{
    type AllUnifsResult = Unification.AllUnifsResult
    protected val allUnifs = Unification.allUnifs _
    protected val remapToCreateCrossRefs = Unification.remapToCreateCrossRefs _
    // protected val effectOnChangedServersCache = 
    //   Unification.effectOnChangedServersCache
  }


}
