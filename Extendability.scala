package ViewAbstraction.ExtendabilityP

import ViewAbstraction._
import ViewAbstraction.collection.ShardedHashMap
import ViewAbstraction.RemapperP.Remapper
import ViewAbstraction.CombinerP.Combiner
import scala.collection.mutable.{HashMap}

/** Utility object, encapsulating the isExtendable function, to test whether a
  * Concretization pre is extendable by a state st given the current set of
  * views.  Used within TransitiontemplateExtender.
  * 
  * @param views the current set of views. */
class Extendability(views: ViewSet){ 
  /* isExtendable
   * |- compatibleWith
   * |- findReferencingView
   */

  /** The type of keys in the cache. */
  private type Key = (Concretization, State)

  /** A cache of results of previous calls to isExtendable.  If a value isn't in
    * the mapping, then that indicates that compatibleWith previously gave
    * only false.  A result of (k,rv) with k >= 0 indicates that
    * compatibleWith gave true, that calls to containsReferencingView gave
    * true for all relevant j in [0..k), and rv[0..k) gives the corresponding
    * referencing views.  */
  private val isExtendableCache = 
    new ShardedHashMap[Key, (Int, Array[ComponentView])] 
    // new HashMap[Key, (Int, Array[ComponentView])] 

  /** Get the value in the cache for key, or (-1,null) if absent. */
  private def getExtendabilityCache(key: Key) = 
    /*synchronized*/{ isExtendableCache.getOrElse(key, (-1, null)) }

  /** Add key -> res to the cache. */
  private def setExtendabilityCache(key: Key, res: (Int, Array[ComponentView])) =
    /*synchronized*/{ isExtendableCache += key -> res }

  /** Is pre extendable by state st, given the current set of views?  (1) Is
    * there an existing view with a renaming of st as principal component, and
    * agreeing with pre on servers and common components?  And (2) for each
    * component cpt of pre that references st, is there an existing view with
    * cpt as principal and containing st (modulo renaming).  If so, return an
    * array of those referencing views found under (2); otherwise return null.
    * 
    * PRE: pre is compatible with SysAbsViews, and pre does not include
    * st.identity.  This means it is enough to check the condition for cpt =
    * st or a non-principal component of pre that references st. ??????
    */
// FIXME: and vice versa for (2)??  Equivalently
  @inline def isExtendable(pre: Concretization, st: State)
      : Array[ComponentView] = {
    require(!singleRef || !useNewReferencingViews)
    // for(v <- pre.toComponentView) require(views.contains(v))
    // require(pre.components.forall(
    //   _.componentProcessIdentity != st.componentProcessIdentity))
    val highlight = false
    // ComponentView0.highlightPrev(pre) && ComponentView0.highlightNext(st)
    if(highlight) println(s"isExtendable($pre, $st)")
    val key = (pre,st); val (k, rv) = getExtendabilityCache(key)

    // Does SysAbsViews contain a view consistent with pre and with a
    // renaming of st as principal component?
    var found = k >= 0 || compatibleWith(pre, st)
    if(highlight) println(s"isExtendable($pre, $st) \nfound = $found; k = $k")
    if(found){
      // If any component cpt of pre references st, then search for a
      // suitable view with a renaming of cpt and st. 
      val components = pre.components; val (f,id) = st.componentProcessIdentity
      // Test whether any component of pre references st
      var j = k max 0; val length = components.length
      val referencingViews = 
        (if(rv != null) rv else new Array[ComponentView](length))
// IMPROVE: does this always hold for j = 0, i.e. is this a preconditon? 
// IMPROVE: this seems inefficient if we got here via 
// instantiatetransitionTemplateViaRef (but this is a low-cost route).
      while(j < length && found){
        if(components(j).hasIncludedParam(f,id)){
          referencingViews(j) = findReferencingView(pre, st, j)
          found = referencingViews(j) != null
        }
        j += 1
      }
      // If st references any component of pre, then test if there's a
      // corresponding view.
// if(false){
//   while(j < length + components.length && found){
//     ???
//   } }

      // Store where we got to
      setExtendabilityCache(key, (if(found) j else j-1, referencingViews))
      if(found) referencingViews else null
    }
    else null
  }

  /** Cached results of calls to Combiner.areUnifiable.  Effectively a map
    * (List[State], List[List[Identity]], List[List[Identity]]) =>
    *  Array[State] => Boolean.   */
  private val compatibleWithCache = new CompatibleWithCache


  /** Is `st` compatible with `pre` given the current views?  Does some renaming
    * of an existing view match `pre.servers`, have `st` as principal
    * component, and agree with `pre.components` on common components?
    * Equivalently, is there a view containing `pre.servers`, with a renaming
    * of `st` as principal component, and such that some renaming of the other
    * components agrees with `pre.components` on common components? */ 
  @inline protected[ExtendabilityP]
  def compatibleWith(pre: Concretization, st: State): Boolean = {
    val highlight = false 
    //  ComponentView0.highlightPrev(pre) && ComponentView0.highlightNext(st)
    if(highlight) println("compatibleWith")
    val servers = pre.servers; val components = pre.components
    // Remap st so it can be the principal component with servers.
    //val st1 = Remapper.remapState(servers.remappingMap, servers.nextArgMap, st)
    val st1 = Remapper.remapToPrincipal(servers, st)
    // IMPROVE: compare with Remapper.remapToPrincipal(servers, st)

    // Create map as identity function on `server` ids and mapping `st1` back
    // to `st`.  Also set otherArgs to contain all parameters in pre not in
    // the range of this map.  This is the base of the renaming applied to a
    // view in `views`, to try to produce a view that matches `servers`, has
    // `st` as principal component, and agrees with `components` on common
    // components
    val map1 = servers.remappingMap; val typeMap = st1.typeMap
    val preBound = pre.getParamsBound
    // All parameters in pre.components but not pre.servers
    val otherArgs: OtherArgMap = Array.tabulate(numTypes)(t =>
      (servers.paramsBound(t) until preBound(t)).toList)
    val ids1 = st1.ids; var j = 0
    while(j < ids1.length){
      val id = ids1(j); val t = typeMap(j)
      if(id >= 0){ 
        val id1 = map1(t)(id); val id2 = st.ids(j)  // map (t,id) -> id2
        if(id1 < 0){ 
          map1(t)(id) = id2; otherArgs(t) = otherArgs(t).filter(_ != id2)
        }
        else assert(id1 == id2)
      }
      j += 1
    } 

    // Get cache corresponding to components, map1 and otherArgs.
    val cache = compatibleWithCache.get( 
      (pre.componentsList, map1.map(_.toList).toList, otherArgs.toList)) 
    // Test whether there is an existing view with a renaming of st as
    // principal component, and the same servers as conc.  
    if(highlight){
      println(s"st1 = $st1"); println(s"map1 = "+Remapper.show(map1))
      println("otherArgs = "+Remapper.show(otherArgs))
    }
    var found = false; val iter = views.iterator(servers, st1)
    while(iter.hasNext && !found){
      val cv1 = iter.next(); assert(cv1.principal == st1)
      if(highlight) println(s"cv1 = $cv1")
      // Does a renaming of the other components of cv1 (consistent with
      // servers and st1) also agree with components on common components?
      // Try to get cached result.
      val cpts1 = cv1.components    // ComponentView0.checkValid(servers,cpts1)
      cache.get(cpts1) match{
        case Some(b) => found = b
        case None =>
          found =
            Combiner.areUnifiable(cv1.components, components, map1, 0, otherArgs)
          // if(highlight) println(s"compatibleWith: $cv1; found = $found")
          cache.add(cpts1,found)
      } // end of match
    } // end of while
    Pools.returnRemappingRows(map1)
    found
  }

  /** Does `views` contain a view with `pre.servers`, `pre.components(j)`
    * (renamed) as principal component, and including a renaming of `st`?  If
    * so, return that view; otherwise return null.
    * 
    * Pre: `pre.components(j)` references `st`.
    * Test case: pre.components = initNodeSt(T0,N0) || aNode(N0,N1), st =
    * initNode(N1), would need a view aNode(N0,N1) || initNode(N1). */
  protected[ExtendabilityP] 
  def findReferencingView(pre: Concretization, st: State, j : Int)
      : ComponentView = {
    val servers = pre.servers; val pCpt = pre.components(j)
    val stF = st.family; val stId = st.id; val pLen = pCpt.length
    // Index of st within pCpt's references
    val stIx = pCpt.indexOf(stF, stId); assert(stIx < pLen) // precondition
    // Find if pCpt's reference to st should be included
    val includeInfo = State.getIncludeInfo(pCpt.cs)
    val includeRef = includeInfo == null || includeInfo(stIx)
    // Rename pCpt to be principal component (map recycled below)
    val map = servers.remappingMap; val nextArgs = servers.nextArgMap
    val pCptR = Remapper.remapState(map, nextArgs, pCpt)
    // st.id gets renamed to stIdR
    val stIdR = map(stF)(stId)
    // Find other components of pre that are referenced by pCpt, and included
    // in views with pCpt as principal.
    val pRefs = new Array[State](pLen); var i = 0
    while(i < pre.components.length){
      if(i != j){
        val cpt = pre.components(i)
        // Index of cpt.componentProcessIdentity in pCpt's parameters
        val ix = pCpt.indexOf(cpt.family, cpt.id)
        if(ix < pLen && (includeInfo == null || includeInfo(ix))) pRefs(ix) = cpt
      }
      i += 1
    }

    // Test whether sysAbsViews contains a view cv1 matching servers, with
    // cptR as the principal component, and containing component with identity
    // (stF,stIdR) unifiable with st.  map (and map2) tries to map pre onto cv1.
    val iter = views.iterator(servers, pCptR); var found = false
    var cv1: ComponentView = null
    while(iter.hasNext && !found){
      cv1 = iter.next(); assert(cv1.principal == pCptR)
      if(includeRef){
        // Test if cv1 contains a component that is a renaming of st under an
        // extension of map. Find component with identity (stF, stIdR) in cv1
        val cpt1 = cv1.find(stF, stIdR)
        if(cpt1 != null){
          // test if cpt1 is a renaming of st under an extension of map. (map2
          // recycled below.)  Note: new map for each cv1.
          var map2 = Unification.unify(map, cpt1, st)
          if(singleRef) found = map2 != null
          else if(map2 != null){
// FIXME: I'm not sure this is correct when we have some excluded refs.
            // Check that all components referenced by pCpt in pre are matched
            // by a corresponding component in cv1.  ok if true for
            // all components so far.
            var k = 1; var ok = true
            while(k < pLen && ok){
              if(pRefs(k) != null){
// FIXME: do those components correspond if there are excluded refs?
                ok = Unification.extendToUnify(map2, cv1.components(k), pRefs(k))
              }
              k += 1
            } // end of inner while
            found = ok; Pools.returnRemappingRows(map2)
          } // end of if(map2 != null)
        } // end of if(cpt1 != null)
        else assert(singleRef) 
      } // end of if(includeRef)
      else
        // Omitted reference, so we approximate this situation by taking cv1
        // to match.
        found = true
    } // end of while(iter.hasNext && !found)
    Pools.returnRemappingRows(map)  
    if(found) cv1 else null
  }


}
