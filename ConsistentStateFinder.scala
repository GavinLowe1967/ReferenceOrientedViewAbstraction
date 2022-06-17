package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
import ViewAbstraction.CombinerP.Combiner
import scala.collection.mutable.{ArrayBuffer,HashMap}

/** Utility object for finding the consistent states for a transition
  * template. */
class ConsistentStateFinder(system: SystemP.System){
  /* consistentStates
   * |- getMaps
   * |- checkCompatible
   */

  /** Get all renamings of cv that: (1) include a component with identity pid;
    * (2) agree with pre on the states of all common components; and (3) can
    * perform e with pre.principal if e >= 0.
    * @return the renaming of the component with identity pid, and all
    * post-states of that component after e (if relevant).  */
  def consistentStates(pre: Concretization, pid: ProcessIdentity, 
    e: EventInt, cv: ComponentView)
      : ArrayBuffer[(State, Array[State])] = {
    val buffer = new ArrayBuffer[(State, Array[State])]()
    val (f,id) = pid; val servers = pre.servers; require(cv.servers == servers)
    require(!pre.hasPid(f,id))
    val preCpts = pre.components; val cpts = cv.components
    // val highlight = servers.servers(0).cs == 32 && servers.servers(1).cs == 33 &&
    //   preCpts(0).cs == 19 && preCpts(1).cs == 10
    if(false) println(s"consistentStates($pre, $pid, $cv")

    val serverRefs = servers.idsBitMap(f)(id)  // do servers reference pid?
    val (fp, idp) = preCpts(0).componentProcessIdentity// id of principal of pre
    // Find all components of cv that can be renamed to a state of pid
    // that can perform e.  Note that it's not enough to consider just the
    // principal: if several views are required for compatibility, the one
    // that is found on the latest ply might not have the relevant state as
    // principal.
    for(i <- 0 until cpts.length){ 
      val st1 = cpts(i)
      // Try to make st1 the component that gets renamed.  Need st1 of family
      // f, and its identity either equal to id, or neither of those
      // identities in the server identities (so the renaming doesn't change
      // servers).
      if(st1.family == f && 
        (st1.id == id || !serverRefs && !servers.idsBitMap(f)(st1.id))){
        // Calculate (in maps) all ways of remapping st1 (consistent with the
        // servers) so that: (1) its identity maps to id; (2) other parameters
        // are injectively mapped either to a parameter in pre.components,
        // but not the servers; or the next fresh parameter.
        val (maps, otherArgs) = 
          try{ getMaps(st1, pid, servers, preCpts) }
          catch{ case UnrepresentableException(renamedState) => 
            println("Not enough identities in script to make\n"+
              s"$pre and\n$cv consistent.\n"+
              s"Renaming of $st1 gives ${renamedState.toString0}")
            sys.exit()
          }
        for((map, renamedState) <- maps){
          // assert(renamedState.representableInScript) 
          val nexts = (
            if(e >= 0) system.nextsAfter(renamedState, e, fp, idp)
            else Array(renamedState) )
          @inline def isNew = !buffer.exists{case (st1,nxts1) => 
            st1 == renamedState && nxts1.sameElements(nexts)}
          if(nexts.nonEmpty && isNew){
            // if(highlight) println(s"renamedState == $renamedState")
// IMPROVE
            if(true || checkCompatible(map, renamedState, cpts, i, preCpts, otherArgs))
              buffer += ((renamedState, nexts))
          }
        } // end of for(map <- maps)
      }
    } // end of for(i <- ...)
    buffer
  } // end of consistentStates

  /** Exception showing renamedState is not representable using values in the
    * script. */
  private case class UnrepresentableException(renamedState: State) 
      extends Exception

  /** Part of the result of getMaps.  Each tuple represents a map, and the
    * renamed states. */
  private type RenamingTuples = Array[(RemappingMap, State)]

  /** Cache of previous results of getMaps. */
  private val mapCache = 
    new HashMap[(State, ProcessIdentity, ServerStates, List[State]), 
      (RenamingTuples, OtherArgMap)]

  /** Calculate all ways of remapping st (consistent with the servers) so
    * that: (1) its identity maps to pid; (2) other parameters are injectively
    * mapped either to a parameter in preCpts, but not the servers; or the
    * next fresh parameter.  
    * @return (1) an Array of (RemappingMap, State) pairs, giving the map and 
    * remapped state; and (2) an OtherArgMap corresponding to servers with pid
    * removed.  
    * @throw  UnrepresentableException if a renamed state is not representable 
    * in the script. */
  private def getMaps(st: State, pid: ProcessIdentity,
    servers: ServerStates, preCpts: Array[State])
      : (RenamingTuples, OtherArgMap) = {
    val preCptsL = preCpts.toList
    mapCache.get(st, pid, servers, preCptsL) match{
      case Some(tuple) => tuple
      case  None =>     // Profiler.count("getMaps: new") ~1.5%
        val (f,id) = pid; val map0 = servers.remappingMap
        val (otherArgs, nextArg) = Remapper.createMaps1(servers, preCpts)
        otherArgs(f) = removeFromList(otherArgs(f), id) 
        nextArg(f) = nextArg(f) max (id+1)
        val maps = Combiner.remapToId(map0, otherArgs, nextArg, st, id)
        // Create corresponding renamed States, and pair with maps
        val mapStates = new RenamingTuples(maps.length); var i = 0
        while(i < maps.length){
          val map = maps(i)
          val renamedState = Remapper.applyRemappingToState(map, st)
          if(!renamedState.representableInScript)
            throw UnrepresentableException(renamedState)
          mapStates(i) = (map, renamedState); i += 1
        }
        mapCache += (st, pid, servers, preCptsL) -> (mapStates, otherArgs)
        (mapStates, otherArgs)
    }
  }

  /** xs with x removed. */
  @inline private def removeFromList(xs: List[Int], x: Int): List[Int] = 
    if(xs.isEmpty) xs
    else{
      val y = xs.head
      if(x == y){ /* assert(!contains(xs.tail, x));*/ xs.tail } 
      else y::removeFromList(xs.tail, x)
    }

  /** Check that renamedState agrees with preCpts on common components, and test
    * whether the remainder of cpts (excluding component i) can be unified
    * with preCpts (based on map and otherArgs1). */
  private def checkCompatible(
    map: RemappingMap, renamedState: State, cpts: Array[State], i: Int,
    preCpts: Array[State], otherArgs: OtherArgMap)
      : Boolean = {
    val pid = renamedState.componentProcessIdentity
    assert(preCpts.forall(!_.hasPID(pid)))
// IMPROVE: I think following is guaranteed to be true
    if(StateArray.agreesWithCommonComponent(renamedState, preCpts)){
      // Renamed state consistent with preCpts. Check a corresponding renaming
      // of the rest of cpts agrees with cpts on common components.  IMPROVE:
      // Trivially true if singleton.
      val otherArgs1 = Remapper.removeParamsOf(otherArgs, renamedState)
      Combiner.areUnifiable(cpts, preCpts, map, i, otherArgs1)
    }
    else{ assert(false); false }
  }
}
