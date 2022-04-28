package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.{ArrayBuffer,HashSet}

/** Object responsible for the unification of cv with pre, suitable for
  * calculating transitions induced by pre -> post upon cv. */
class EffectOnUnification(
  pre: Concretization, post: Concretization, cv: ComponentView){
  require(!singleRef) // require(!newEffectOn)

  import Unification.CombineResult 
    // = ArrayBuffer[(RemappingMap, Array[State], UnificationList)]
  import EffectOnUnification.MatchingTuple

  /* Relationship of main functions:
   * 
   * apply
   * |--Unification.allUnifs
   * |--isSufficientUnif
   * |--mkOtherArgsBitMap
   * |  |--addIdsFromNewRef
   * |--extendUnif
   * |  |--Unification.combine1
   * |--extendUnifSingleRef                    (~95% of time with lazySet)
   *    |--EffectOnUnification.remapToCreateCrossRefs  (~25%)
   *    |--getOtherArgsBitMapForSingleRef              (~12%)
   *    |--Unification.getCombiningMaps                (~25%)
   *    |--makeSecondaryInducedTransitions             (~10%)
   */ 

  /* A few object variables, extracted directly from pre, post and cv, used in
   * several functions. */
  private val servers = pre.servers
  require(servers == cv.servers && servers.isNormalised)
  private val postServers = post.servers
  private val preCpts = pre.components; private val postCpts = post.components
  require(preCpts.length == postCpts.length)
  private val cpts = cv.components
  if(debugging) StateArray.checkDistinct(cpts)
  private val (cvpf, cvpid) = cv.principal.componentProcessIdentity

  // IMPROVE
  val highlight = false &&
    preCpts.length == 2 && preCpts(0).cs == 15 && preCpts(1).cs == 7 &&
      cpts(0).cs == 8 && cpts(0).ids(0) == 1
    // pre.servers.servers(1).cs == 100 && post.servers.servers(5).cs == 113 &&
    //   preCpts.length == 2 && cv.components.length == 2 &&
    //   preCpts(0).cs == 66 && preCpts(1).cs == 13 && preCpts(1).ids(2) == 3 &&
    //   preCpts.sameElements(cv.components)

  /** Identities of components of pre. */
  val preIds = 
    Array.tabulate(preCpts.length)(i => preCpts(i).componentProcessIdentity)

  /** Identities of components of cv. */
  val cvIds = Array.tabulate(cpts.length)(i => cpts(i).componentProcessIdentity)

  /** Identities of components of pre that match the family of cv.principal. */
  private val preMatchingIds = {
    var ids = List[Identity](); var i = 0
    while(i < preCpts.length){
      val c = preCpts(i); i += 1; if(c.family == cvpf) ids ::= c.ids(0)
    }
    ids
  }

  /** For each parameter x of states, the list of positions (component number,
    * parameter number) where x appears.  size gives the number of parameters
    * of each type. */
  def mkPositionMap(size: Array[Int], states: Array[State])
      : Array[Array[List[(Int,Int)]]] = {
    val pMap = Array.tabulate(numTypes)( t => 
      Array.fill(size(t))(List[(Int,Int)]()) )
    for(i <- 0 until states.length){
      val pids = states(i).processIdentities
      for(j <- 0 until pids.length){
        val (t,x) = pids(j)
        if(!isDistinguished(x)) pMap(t)(x) ::= (i,j)
      }
    }
    pMap
  }

  /** For each parameter x of preCpts, the list of positions (component number,
    * parameter number) where x appears.  IMPROVE: maybe this should be stored
    * in pre.  */
  val prePositionMap: Array[Array[List[(Int,Int)]]] = 
    mkPositionMap(pre.getParamsBound, preCpts)
  // IMPROVE
  //for(t <- 0 until numTypes; pairs <- prePositionMap(t))
  // assert(pairs.forall(_._1 < preCpts.length))

  /** For each parameter x of cv, the list of positions (component number,
    * parameter number) where x appears.  IMPROVE: maybe this should be stored
    * in cv.  */
  val cvPositionMap: Array[Array[List[(Int,Int)]]] = 
    mkPositionMap(cv.getParamsBound, cpts)

  /** In the case of singleRef, secondary components of the transition that
    * might gain a reference to c2 = cv.principal (without unification): all
    * pairs (i,id) (i >= 1) such that the i'th component c1 of pre changes
    * state, and id is a parameter of c1 in the post state that might
    * reference c2. We will subsequently form secondary induced transitions
    * with c1 as the principal component, referencing c2 (renamed). */
  private val c2Refs: List[(Int,Identity)] =
    if(singleRef) getCrossReferences() else List[(Int,Identity)]()
// IMPROVE: consider omitted references here

  import Unification.UnificationList // = List[(Int,Int)]
  // Contains (i,j) if cpts(i) is unified with preCpts(j)

  // A representation of map |> post.servers
  import ServersReducedMap.ReducedMap 

  type CombineResult1 = 
    ArrayBuffer[(RemappingMap, Array[State], UnificationList, ReducedMap)]

  /** The part of the result corresponding to secondary induced transitions.
    * The Int field is the index of the component in pre/post that gains
    * access to cv.principal. */
  type CombineResult2 = ArrayBuffer[(Array[State], UnificationList, Int)]

  /** Variables in which we build up the result. */
  private val result = new CombineResult1
  private val result2 = new CombineResult2

  /** A NextArgMap, containing values greater than anything in pre or post. */
  private val nextArg: NextArgMap = pre.getNextArgMap
  post.updateNextArgMap(nextArg)

  /** Bit map indicating which components have changed state. */
  private val changedStateBitMap = getChangedStateBitMap()

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
    * are distinct post symmetry reduction).  
    * 
    * The first component of the returned result contains tuples (map, cpts,
    * unifs) where map is the remapping function, cpts is the remapped
    * components, and a UnificationList that contains (j,i) whenever
    * cv.components(j) unifies with pre.components(i).
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
  def apply(): (CombineResult1, CombineResult2) = {
    // IMPROVE: some of the initial calculations depends only on pre and post, so
    // could be stored with the transition.
    val princRenames = c2Refs.map(_._2) // normally empty; sometimes singleton
    require(singleRef || princRenames.isEmpty)
    val changedServers = servers != post.servers
    val map0 = servers.remappingMap1(cv.getParamsBound)
    // All params in post.servers but not in pre.servers, as a bitmap.
    val newServerIds: Array[Array[Boolean]] = 
      ServerStates.newParamsBitMap(servers, post.servers)

    // Get all ways of unifying pre and cv. 
    val allUs = Unification.allUnifs(map0, pre/*Cpts*/, cpts)
    // assert(allUs.distinct.length == allUs.length)
    var ix = 0
    while(ix < allUs.length){
      val (map1, unifs) = allUs(ix); ix += 1
      //if(highlight) println(s"*unifs = $unifs, map1 = "+Remapper.show(map1)) 
      // Does this create a cross reference from a secondary component to the
      // principal of cv (with singleRef)?
      val acquiredCrossRef = princRenames.contains(map1(cvpf)(cvpid))
      // Do we need to consider this combination?  Described in optimisations
      // in the paper.  For singleRef, it describes when it is necessary to
      // consider primary induced transitions.
      val sufficientUnif = 
        isSufficientUnif(changedServers, unifs, acquiredCrossRef)
      //if(highlight) 
      //  println(s"sufficientUnif = $sufficientUnif; c2Refs = $c2Refs")
      if(c2Refs.nonEmpty || sufficientUnif){
        val otherArgsBitMap = mkOtherArgsBitMap(newServerIds, unifs)
        if(singleRef) 
          extendUnifSingleRef(unifs, map1, otherArgsBitMap, sufficientUnif)
        else extendUnif(unifs, map1, otherArgsBitMap)
      }
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
    * @param acquiredCrossRef with singleRef, has a secondary component acquired 
    * a reference to the principal of cv? */
  @inline private def isSufficientUnif(
    changedServers: Boolean, unifs: UnificationList, acquiredCrossRef: Boolean)
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
      if(unifs.length == cpts.length && unifs.contains((0,0))) false
// IMPROVE:  case below?
      else // changedServers || changingUnif
        if(changedServers) true // unifs.nonEmpty || !cv.containsDoneInduced(postServers)
      else changingUnif
    } // end of if(singleRef)
    else if(changedServers)// {
    //   if(changingUnif) true else cv.addDoneInduced(postServers, unifs)
    // }
      unifs.nonEmpty || cv.addDoneInduced(postServers)
      // Note, this can't be strengthened to
      // changingUnif || effectOnChangedServersCache.add((cv, postServers))
      // If there are two different ways of performing unification with a 
      // component that doesn't change state, this will find just one of them.
    else changingUnif
  }

  /** Create a bit map corresponding to an OtherArgMap and containing all
    * values: (1) in newServerIds (parameters in post.servers but not
    * pre.servers), or (2) in post.cpts for a unified parameter if not in
    * (pre.)servers; (3) in post.cpts for a component to which cv.principal
    * gains a reference; But excluding parameters of servers in all cases.  */
  @inline private 
  def mkOtherArgsBitMap(newServerIds: BitMap, unifs: UnificationList): BitMap = {
    // (1) parameters in newServerIds
    val otherArgsBitMap = newServerIds.map(_.clone); var us = unifs
    while(us.nonEmpty){
      val (j, i) = us.head; us = us.tail
      // (2) Add parameters of postCpts(i), which is unified with a component
      // of cv.
      postCpts(i).addIdsToBitMap(otherArgsBitMap, servers.idsBitMap) 
      // (3) If this is the unification of the principal of cv, which changes
      // state and gains a reference to another component c, include the
      // parameters of c from postCpts.
      if(j == 0 && changedStateBitMap(i)) addIdsFromNewRef(otherArgsBitMap, i)
    }
    otherArgsBitMap
  }

  /** Add to otherArgsBitMap any parameters of a component c to which preCpts(i)
    * gains a reference as the result of the transition. */ 
  @inline private 
  def addIdsFromNewRef(otherArgsBitMap: Array[Array[Boolean]], i: Int) = {
    val prePids = preCpts(i).processIdentities
    val postPids = postCpts(i).processIdentities
    val serverIds = servers.idsBitMap
    // Find which parameters are gained
    for(k <- 1 until postPids.length){
      val pid = postPids(k)
      if(!isDistinguished(pid._2) && !prePids.contains(pid)){
        val c = StateArray.find(pid, postCpts)
        // Assumptions imply pid must be in postCpts, except under singleRef.
        if(c != null) c.addIdsToBitMap(otherArgsBitMap, serverIds)
        else assert(singleRef)
      }
    }
  }

  /** Extend map1 with unifications unifs, corresponding to transitions induced
    * by the transition pre -> post on cv.
    * 
    * Parameters must be remapped consistent with map1.  Parameters undefined
    * in map1 can be mapped: (1) to a parameter in otherArgsBitMap (other than
    * in the range of map1); or (2) a fresh value, given by nextArg.  However,
    * identities cannot be mapped to identities of postCpts (=
    * post.components) (since that would imply unification).  Each remapped
    * state and corresponding unifications is added to result. */
  @inline private def extendUnif(unifs: UnificationList,
    map1: RemappingMap, otherArgsBitMap: BitMap)
      : Unit = {
    // if(debugging) assert(Remapper.isInjective(map1), Remapper.show(map1))
    assert(!singleRef)
    // Remove values in ran map1
    Remapper.removeFromBitMap(map1, otherArgsBitMap)
    // Convert to OtherArgMap
    val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
    // Values that identities can be mapped to: values in otherArgs, but not
    // identities of components in post; update otherArgsBitMap to record.
    StateArray.removeIdsFromBitMap(postCpts, otherArgsBitMap)
    // Create primary induced transitions.
    Unification.combine1(
      map1, otherArgs, otherArgsBitMap, nextArg, unifs, cpts, result)
  } // end of extendUnif


  /** Extend a unification in the case of singleRef.  Extend otherArgsBitMap0 so
    * that if a component of cv gets a reference to a component c of preCpts,
    * then the parameters of c are included in otherArgsBitMap.  Then create
    * induced transitions.   */
// IMPROVE: not all of these are needed for secondary induced transitions
  @inline private def extendUnifSingleRef(
    unifs: UnificationList, map0: RemappingMap, otherArgsBitMap0: BitMap,
    sufficientUnif: Boolean)
  = {
    require(singleRef)
    // Extend map0 to consider all combinations of mapping an identity in cpts
    // to match a non-identity parameter in preCpts, or a non-identity
    // parameter in preCpts to match an identity in cpts (but not matching any
    // identities); this includes the case of mapping no such parameters.
    // Each resulting map (map1 below) is paired with a list of tuples
    // ((i1,j1), (i2,j2)) indicating that parameter j2 of cpts(i2) is mapped
    // to match paramter j1 of preCpts(i1) (precisely one of j1 and j2 will be
    // 0).
    val crossRefs = 
      // if(false)
      //   EffectOnUnification.remapToCreateCrossRefs(preCpts, cpts, map0)
      // else
        newRemapToCreateCrossRefs(map0)
    //if(highlight) 
    //  println("extendUnifSingleRef; crossRefs length = "+crossRefs.length)
    var i = 0
    while(i < crossRefs.length){
      val (map1, tuples) = crossRefs(i); i += 1
      // if(highlight) println(s"tuples = $tuples, map1 = "+Remapper.show(map1))
      // Profiler.count("tuples size "+tuples.length) -- mostly 0 or 1
      // Get other arg BitMap for this case. 
      val otherArgsBitMap = getOtherArgsBitMapForSingleRef(
        map1, otherArgsBitMap0, tuples)
      // Convert to OtherArgMap
      val otherArgs = Remapper.makeOtherArgMap(otherArgsBitMap)
      // if(highlight) println("otherArgs = "+otherArgs.mkString("; "))
      // Values that identities can be mapped to: values in otherArgs, but not
      // parameters in preCpts; update otherArgsBitMap to record.
      StateArray.removeParamsFromBitMap(preCpts, otherArgsBitMap)
      // Create primary induced transitions.
      if(sufficientUnif){
        val res0 = new ArrayBuffer[RemappingMap]
        Unification.getCombiningMaps(
          map1, otherArgs, otherArgsBitMap, nextArg, cpts, res0)
        var j = 0
        while(j < res0.length){
          val map11 = res0(j); j += 1
          // assert(!(j until res0.length).exists(i =>  
          //   (0 until numTypes).forall(t => map11(t).sameElements(res0(i)(t)))))
          val reducedMapInfo: ReducedMap = 
            if(unifs.isEmpty) Remapper.rangeRestrictTo(map11, postServers)
            else null
          if(unifs.nonEmpty || 
            !cv.containsDoneInducedPostServersRemaps(
              postServers, reducedMapInfo)){
            val newCpts = Remapper.applyRemapping(map11, cpts)
// IMPROVE
if(false){
  val matches = result.filter{ case (_,newCpts2,unifs2,_) => 
    newCpts2.sameElements(newCpts) && unifs2 == unifs }
  assert(matches.isEmpty,
    s"\nnewCpts = "+StateArray.show(newCpts)+s"; unifs = $unifs\n"+
      "map1 = "+Remapper.show(map1)+"; otherArgs = "+otherArgs.mkString("; ")+
      "; map11 = "+Remapper.show(map11)+s"; tuples = $tuples\n"+
      s"crossRefs = "+crossRefs.map{ case (mapX,tuples2) => 
        "("+Remapper.show(mapX)+"; "+tuples2+")" }.mkString("; ")+
      s"\nresult = "+result.map{ case (mapX,newCpts2,unifs2,_) =>
        Remapper.show(mapX)+"; "+StateArray.show(newCpts2)+"; "+unifs2 }
      .mkString("\n  "))
} 
            //if(highlight) println("Adding "+StateArray.show(newCpts))
            result += ((map11, newCpts, unifs, reducedMapInfo))
          }
        }
      } // end of if(sufficientUnif)
      makeSecondaryInducedTransitions(map1, otherArgs, otherArgsBitMap, unifs)
    } // end of outer for loop.
  } // end of extendUnifSingleRef

  /** Extend otherArgsBitMap0.  Add parameters of components c of preCpts such
    * that a component of map1(cv) has a reference to c, or vice versa; such
    * components c are identified by the first index in an element of tuples.
    * Also remove values in ran map1, and all identities in preCpts. */
  @inline private def getOtherArgsBitMapForSingleRef(
    map1: RemappingMap, otherArgsBitMap0: BitMap, 
    tuples: List[((Int,Int),(Int,Int))])
      : BitMap = {
    // Clone, to avoid interference between different iterations.
    val otherArgsBitMap = otherArgsBitMap0.map(_.clone)
    // Indices of components of preCpts for which we have added the parameters
    val doneIndices = new Array[Boolean](preCpts.length) 
    var tups = tuples
    while(tups.nonEmpty){
      val i1 = tups.head._1._1; tups = tups.tail
      //assert(i1 < preCpts.length, s"pre = $pre\n cv = $cv\ntuples = $tuples")
      if(!doneIndices(i1)){
        doneIndices(i1) = true 
        preCpts(i1).addIdsToBitMap(otherArgsBitMap, servers.idsBitMap, 1)
      }
    }
    // }
    // Remove identities of components in preCpts
    var i = 0
    while(i < preCpts.length){
      val (t,id) = preCpts(i).componentProcessIdentity; i += 1
      otherArgsBitMap(t)(id) = false
    }

    // IMPROVE: we need only map parameters of cpts(i2) like this, where
    // i2 is the relevant index in the current tuple.
    // for(cpt <- preCpts) cpt.addIdsToBitMap(otherArgsBitMap, servers.numParams)
    // Remove values in ran map1
    Remapper.removeFromBitMap(map1, otherArgsBitMap)
    otherArgsBitMap
  }

  /** Create information about secondary induced transitions, and add them to
    * result2.  For each (k,p) in c2Refs, try to map cv.principal's identity
    * to p, so c = postCpts(k) has a reference to cv.principal in p.  Remap
    * according to map1, otherArgs, otherArgsBitMap, nextArg, but also mapping
    * parameters to parameters of c. */
  @inline private def makeSecondaryInducedTransitions( 
    map1: RemappingMap, otherArgs0: OtherArgMap, otherArgsBitMap0: BitMap,  
    unifs: UnificationList)
  = {
    //if(highlight) println("makeSecondaryInducedTransitions")
    // IMPROVE
    for(f <- 0 until numTypes; id <- otherArgs0(f); 
        id1 <- 0 until map1(f).length)
      assert(map1(f)(id1) != id)
    /* Build remappings for secondary induced transitions corresponding to
     * component k acquiring a reference to cv.principal in parameter id. */
    @inline def mkSecondaryRemaps(k: Int, id: Int) = {
      // if(highlight) println(s"mkSecondaryRemaps($k, $id)")
      // clone otherArgs0, otherArgsBitMap, removing (cvpf,id)
      val otherArgs = new Array[List[Identity]](numTypes); var f = 0
      while(f < numTypes){
        if(f == cvpf) otherArgs(f) = otherArgs0(f).filter(_ != id)
        else otherArgs(f) = otherArgs0(f)
        f += 1
      }
      val otherArgsBitMap = otherArgsBitMap0.map(_.clone)
      otherArgsBitMap(cvpf)(id) = false
      require(map1(cvpf)(cvpid) == id && 
        postCpts(k).processIdentities.contains((cvpf,id)))
      // For each other parameter of postCpts(k), if not in ran map1, add to
      // otherArgs, and to otherArgsBitMap if not an identity in postCpts.
      for((t,id1) <- postCpts(k).processIdentities)
        if(id1 != id && !isDistinguished(id1) && 
            !contains(map1(t),id1) && !contains(otherArgs(t),id1)){
          otherArgs(t) ::= id1
          if(StateArray.findIndex(postCpts, t, id1) < 0)
            otherArgsBitMap(t)(id1) = true
        }
      val tempRes = new CombineResult
      for(f <- 0 until numTypes; id <- otherArgs(f);
          id1 <- 0 until map1(f).length)
        assert(map1(f)(id1) != id, 
          Remapper.show(map1)+"\n"+otherArgs.mkString(";"))
      // if(highlight) println(Remapper.show(otherArgs))
      Unification.combine1(
        map1, otherArgs, otherArgsBitMap, nextArg, unifs, cpts, tempRes)
      for((_, newSts, us, _) <- tempRes){ // IMPROVE
        //if(highlight) println(s"adding (${StateArray.show(newSts)}, $us, $k)")
        assert(us eq unifs); StateArray.checkDistinct(newSts)
        result2 += ((newSts, us, k))
      }
    } // end of mkSecondaryRemaps

    for((k,p) <- c2Refs){
      //if(highlight)
      //  println(s"k = $k, p = $p, map1(cvpf)(cvpid) = "+map1(cvpf)(cvpid))
      // Can we map (cvpf,cvpid) to p?
      if(map1(cvpf)(cvpid) == p) mkSecondaryRemaps(k, p)
      else if(map1(cvpf)(cvpid) < 0 && !contains(map1(cvpf), p) && 
          !contains(preMatchingIds, p)){
        // Consider mapping cvpid to p (and backtrack)
        map1(cvpf)(cvpid) = p; // assert(!otherArgs0(cvpf).contains(p))
        mkSecondaryRemaps(k, p); map1(cvpf)(cvpid) = -1
      }
    }
  }

  /** Bitmap showing which components changed state between preCpts and
    * postCpts. */
  @inline private 
  def getChangedStateBitMap(): Array[Boolean] = {
    val changedStateBitMap = new Array[Boolean](preCpts.length); var i = 0
    while(i < preCpts.length){
      changedStateBitMap(i) = preCpts(i) != postCpts(i); i += 1
    }
    changedStateBitMap
  }

// IMPROVE: in the calculation of c2Refs, I think we can omit params of
// pre.servers other than cv.principal's identity.
// IMPROVE: could we have more simply achieved the effect of c2Refs by using
// cv with pre.principal as principal, and c2 as secondary component?  This
// assumes pre.principal has a reference to c2, which seems reasonable.

  /** Identify secondary components that can gain a reference to a component of
    * type cvpf (the type of cv.principal.family).  All pairs (i,id) (with i
    * >= 1) such that the i'th component c1 changes state between preCpts and
    * postCpts, and id is a new included non-distinguished parameter of c1 of
    * family cvpf in the post state. */
  @inline private def getCrossReferences(): List[(Int,Identity)] = {
    require(singleRef)
    var result = List[(Int,Identity)](); var i = 1
    while(i < preCpts.length){
      if(preCpts(i) != postCpts(i)){
        val c1 = postCpts(i); val c1Params = c1.ids; var j = 1
        while(j < c1Params.length){
          if(c1.includeParam(j) && c1.typeMap(j) == cvpf){
            val p = c1Params(j)
            // Check: non-distiguished, not an id in preCpts, new param in c1
            if(!isDistinguished(p) && !preCpts(i).hasIncludedParam(cvpf,p))
// IMPROVE: think about above; should it be hasParam? 
              result ::= (i, p)
          }
          j += 1
        } // end of inner while
      }
      i += 1
    } // end of outer while
    if(false) println(s"getCrossReferences: $result")
    result
  }

  /** All ways of extending map (over cpts) so that an identity in cpts matches
    * a non-identity parameter in preCpts, or a non-identity parameter in
    * preCpts matches an identity in cpts; but no identity should map to an
    * identity.
    * @return the resulting map, together with a list of tuples
    * ((i1,j1), (i2,j2)) indicating that parameter j2 of cpts(i2) is mapped to
    * match parameter j1 of preCpts(i1); precisely one of j1 and j2 will be
    * 0. */
  def newRemapToCreateCrossRefs(map: RemappingMap)
      : ArrayBuffer[(RemappingMap, List[MatchingTuple])] = {
    val result = new ArrayBuffer[(RemappingMap, List[MatchingTuple])]
    // Bitmap showing the range of map
    val inRangeBitMap = Remapper.rangeBitMap(map)

    /* Perform renamings starting with parameter (t,x) mapping to (t,y).  
     * Consider cases in lexicographic order of (t,x,y).  All updates to map
     * and inRangeBitMap are backtracked. */
    def rec(tuples: List[MatchingTuple], t: Type, x: EventInt, y: EventInt)
        : Unit =
      if(t == numTypes) // finished this branch
        result += ((Remapper.cloneMap(map), tuples))
      else if(x == map(t).size) rec(tuples, t+1, 0, 0) // move to next type
      else if(y == prePositionMap(t).size)  
        rec(tuples, t, x+1, 0) // Move to next param of cv
    else{
      // try to map (t,x) -> (t,y)
      if(map(t)(x) < 0 && !inRangeBitMap(t)(y) && 
        // Precisely one of (t,x), (t,y) is an identity
        (cvIds.contains((t,x)) ^ preIds.contains((t,y)))){
        map(t)(x) = y; inRangeBitMap(t)(y) = true // temporary update
        val newTuples = 
          crossProduct(prePositionMap(t)(y), cvPositionMap(t)(x)) ++ tuples
        rec(newTuples, t, x, y+1)
        map(t)(x) = -1; inRangeBitMap(t)(y) = false  // backtrack (*)
      }
      // Also just advance (whether or not we did the if).  If already have
      // (t,x) -> (t,y), add relevant tuples here.
      val newTuples = 
        if(map(t)(x) == y) 
          crossProduct(prePositionMap(t)(y), cvPositionMap(t)(x)) ++ tuples
        else tuples
      rec(newTuples, t, x, y+1)
    }

    rec(List[MatchingTuple](), 0, 0, 0)
    result
  }

  /** Cross product of ps1 and ps2. */
  def crossProduct(ps1: List[(Int,Int)], ps2 : List[(Int,Int)]) = 
    for(p1 <- ps1; p2 <- ps2) yield (p1,p2)

}

// ==================================================================

object EffectOnUnification{
  def combine(pre: Concretization, post: Concretization, cv: ComponentView) = 
    new EffectOnUnification(pre, post, cv)()

  /** A tuple in a remapping from cpts to preCpts.  Each tuple ((i1,j1),(i2,j2))
    * indicates that parameter j2 of cpts(i2) is mapped to match parameter j1
    * of preCpts(i1).  Precisely one of j1 and j2 equals 0. */
  type MatchingTuple = ((Int,Int), (Int, Int))

// IMPROVE: I think we only use i1.

// IMPROVE: I think there's some redundancy in what follows.  Maybe restrict
// to i1 components, and remove duplicates.  cf old assertion in
// EffectOn.apply line 100.

/*
  /** All ways of extending map (over cpts) so that an identity in cpts matches
    * a non-identity parameter in preCpts, or a non-identity parameter in
    * preCpts matches an identity in cpts; but no identity should map to an
    * identity.
    * @return the resulting map, together with a list of tuples
    * ((i1,j1), (i2,j2)) indicating that parameter j2 of cpts(i2) is mapped to
    * match parameter j1 of preCpts(i1); precisely one of j1 and j2 will be
    * 0. */
  private def remapToCreateCrossRefs(
    preCpts: Array[State], cpts: Array[State], map: RemappingMap)
      : ArrayBuffer[(RemappingMap, List[MatchingTuple])] = {
    val highlight = false // IMPROVE

    // Bit maps (indexed by component number, param number) showing which
    // parameters of cpts can be mapped and which components of preCpts can be
    // mapped onto: all identities; and non-identities those that are not
    // distinguished, and do not match any identity in cpts, resp preCpts.
    val domBitMap = getDomBitMap(cpts); val rangeBitMap = getRangeBitMap(preCpts)
    val result = new ArrayBuffer[(RemappingMap, List[MatchingTuple])]
    // Bitmap showing the range of map
    val inRangeBitMap = Remapper.rangeBitMap(map)
    // if(highlight){
    //   println("domBitMap = "+domBitMap.map(_.mkString(", ")).mkString("; "))
    //   println("rangeBitMap = "+rangeBitMap.map(_.mkString(", ")).mkString("; "))
    // }

    // Next component of preCpts(i1) to try mapping on to.  The minimum j in
    // [j1 .. preCpts(i1).length) s.t. rangeBitMap(i1)(j); or
    // preCpts(i1).length if there is no such.
    @inline def advanceInPreCpts(i1: Int, j1: Int) = {
      var j = j1
      while(j < preCpts(i1).length && !rangeBitMap(i1)(j)) j += 1
      j
    }
    // Next component of cpts(i2) to try mapping.  The minimum j in [j2
    // .. cpts(i2).length) s.t. domBitMap(i2)(j); or cpts(i2).length if there
    // is no such.
    @inline def advanceInCpts(i2: Int, j2: Int) = {
      var j = j2
      while(j < cpts(i2).length && !domBitMap(i2)(j)) j += 1
      j
    }

    /* Consider extending map and tuples so as to map parameter j2 of cpts(i2) to
     * match parameter j1 of preCpts(i1); then continue, considering
     * parameters in lexicographic order.  All updates to map are backtracked.
     * Pre: (1) Exactly one of j1 and j2 is 0.  (2) rangeBitMap(i1)(j1), or one
     * of i1, j1 is out of range. */
    def rec(tuples: List[MatchingTuple], i1: Int, j1: Int, i2: Int, j2: Int)
        : Unit = {
      assert((j1 == 0) ^ (j2 == 0), s"j1 = $j1; j2 = $j2")
      assert(i1 == preCpts.length || j1 == preCpts(i1).length ||
        rangeBitMap(i1)(j1))
      assert(i2 == cpts.length || j2 == cpts(i2).length || domBitMap(i2)(j2), 
        s"i1 = $i1, j1 = $j1, i2 = $i2, j2 = $j2")
      if(i1 == preCpts.length)  // finished this branch
        result += ((Remapper.cloneMap(map), tuples))
      // Various cases of advancing
      else if(j1 == preCpts(i1).length) // Move to next cpt of preCpts
        rec(tuples, i1+1, 0, 0, advanceInCpts(0,1))
      else if(i2 == cpts.length) 
        // At end of cpts; advance to next parameter in preCpts(i1) that can
        // be mapped to.
        rec(tuples, i1, advanceInPreCpts(i1,j1+1), 0, 0) 
      else if(j2 == cpts(i2).length){ // advance to next component of cpts
        if(i2+1 == cpts.length) rec(tuples, i1, advanceInPreCpts(i1,j1+1), 0, 0)
        else rec(tuples, i1, j1, i2+1, if(j1 == 0) advanceInCpts(i2+1,1) else 0)
      }
      else{
        assert(domBitMap(i2)(j2))
        // Try to map id2 to match id1
        val id1 = preCpts(i1).ids(j1); val id2 = cpts(i2).ids(j2)
        val t = preCpts(i1).typeMap(j1)
        assert(!isDistinguished(id1) && !isDistinguished(id2))
        if(t == cpts(i2).typeMap(j2) && map(t)(id2) < 0 && 
          !inRangeBitMap(t)(id1) ){
          map(t)(id2) = id1; inRangeBitMap(t)(id1) = true // temporary update (*)
          val newTuples = ((i1,j1),(i2,j2))::tuples
          // Advance
          if(j1 == 0) rec(newTuples, i1, j1, i2, advanceInCpts(i2, j2+1))
          else rec(newTuples, i1, j1, i2+1, 0)
          map(t)(id2) = -1; inRangeBitMap(t)(id1) = false  // backtrack (*)
        }
        // Also just advance (whether or not we did the if).  If already
        // matched, add tuple here.
        val newTuples = 
          if(t == cpts(i2).typeMap(j2) && map(t)(id2) == id1)
            ((i1,j1),(i2,j2))::tuples
          else tuples
        if(j1 == 0) rec(newTuples, i1, j1, i2, advanceInCpts(i2, j2+1))
        else rec(newTuples, i1, j1, i2+1, 0)
      }
    } // end of rec

    val j1 =  advanceInPreCpts(0,0)
    rec(List[MatchingTuple](), 0, j1, 0, if(j1 == 0) advanceInCpts(0,1) else 0)
    result
  }
 */

  /** Bit map (indexed by component number, param number) showing which
    * parameters of preCpts can be mapped onto within remapToCreateCrossRefs:
    * all identities; and non-identities those that are not distinguished, and
    * do not match any identity in preCpts. */
  @inline private def getRangeBitMap(preCpts: Array[State]): BitMap = {
    val preIds = Array.tabulate(preCpts.length)(
      i => preCpts(i).componentProcessIdentity)
    val rangeBitMap = new Array[Array[Boolean]](preCpts.length); var i = 0
    while(i < preCpts.length){
      val cpt = preCpts(i); rangeBitMap(i) = new Array[Boolean](cpt.length)
      rangeBitMap(i)(0) = true; var j = 0 // IMPROVE: j = 1?
      while(j < cpt.length){
        val (t,p) = cpt.processIdentity(j)
        if(!isDistinguished(p) && !preIds.contains((t,p))){
          rangeBitMap(i)(j) = true; assert(j != 0)
        }
        j += 1
      } // end of inner while
      i += 1
    } // end of outer while
    rangeBitMap
  }

  /** Map (indexed by component number, param number) showing which parameters
    * of preCpts can be mapped onto within remapToCreateCrossRefs: a value
    * of 0 represents that it cannot be mapped onto; a value of 1 represents
    * that it can be mapped, but that this is not the first instance of the
    * parameter, so it can be mapped onto only if the earlier instance was
    * mapped onto; */
  //@inline def getRangeMap(preCpts: Array[State]): Array[Array[Int]] = ???

  /** Similar bit map for cpts, showing which params can be mapped: all
    * identities; and all non-identities that are not distinguished, and do
    * not match any identity in cpts. */
  @inline private def getDomBitMap(cpts: Array[State]): BitMap = {
    val ids = Array.tabulate(cpts.length)(i => cpts(i).componentProcessIdentity)
    val domBitMap = new Array[Array[Boolean]](cpts.length); var i = 0
    while(i < cpts.length){
      val cpt = cpts(i); domBitMap(i) = new Array[Boolean](cpt.length)
      domBitMap(i)(0) = true; var j = 0
      while(j < cpt.length){
        val (t,p) = cpt.processIdentity(j)
        if(!isDistinguished(p) && !ids.contains((t,p))) domBitMap(i)(j) = true
        j += 1
      } // end of inner while
      i += 1
    } // end of outer while
    domBitMap
  }

  /** Hooks for testing. */
  trait Tester{
    // protected val remapToCreateCrossRefs = 
    //   EffectOnUnification.remapToCreateCrossRefs _ 
  }
}
