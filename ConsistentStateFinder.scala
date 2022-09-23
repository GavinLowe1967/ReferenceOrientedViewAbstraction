package ViewAbstraction

import ViewAbstraction.RemapperP.Remapper
import ViewAbstraction.CombinerP.Combiner
import scala.collection.mutable.{ArrayBuffer,HashMap}
import collection.ShardedHashMap

/** Utility object for finding the consistent states for a transition
  * template. */
class ConsistentStateFinder(system: SystemP.System){
  /* consistentStates
   * |- getRenamedStates
   * |  |- Combiner.remapToId
   * |- processRenamedState
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
    val serverRefs = servers.idsBitMap(f)(id)  // do servers reference pid?
    val (fp, idp) = preCpts(0).componentProcessIdentity// id of principal of pre
    var i = 0
    // Find all components of cv that can be renamed to a state of pid
    // that can perform e.  Note that it's not enough to consider just the
    // principal: if several views are required for compatibility, the one
    // that is found on the latest ply might not have the relevant state as
    // principal.
    while(i < cpts.length){
      val st1 = cpts(i); i += 1
      // Try to make st1 the component that gets renamed.  Need st1 of family
      // f, and its identity either equal to id, or neither of those
      // identities in the server identities (so the renaming doesn't change
      // servers).
      if(st1.family == f && 
        (st1.id == id || !serverRefs && !servers.idsBitMap(f)(st1.id))){
        // All ways of remapping st1 (consistent with the servers) so that:
        // (1) its identity maps to id; (2) other parameters are injectively
        // mapped either to a parameter in pre.components, but not the
        // servers; or the next fresh parameter.
        val renamedStates = 
          try{ getRenamedStates(st1, pid, servers, preCpts) }
          catch{ case UnrepresentableException(renamedState) => 
            println("Not enough identities in script to make\n"+
              s"$pre and\n$cv consistent.\n"+
              s"Renaming of $st1 gives ${renamedState.toString0}")
            sys.exit()
          }
        var j = 0
        while(j < renamedStates.length){
          val renamedState = renamedStates(j); j += 1
          processRenamedState(renamedState, e, fp, idp, buffer)
        } // end of inner while
      }
    } // end of outer while
    buffer
  } // end of consistentStates


  /** Find the next states from renamedState after e, if >=0, and add to
    * buffer. */
  private def processRenamedState(
    renamedState: State, e: EventInt, fp: Family, idp: Identity, 
    buffer: ArrayBuffer[(State, Array[State])])
  = {
    // assert(renamedState.representableInScript)
    val nexts = 
      if(e >= 0) system.nextsAfter(renamedState, e, fp, idp)
      else Array(renamedState) 
    if(nexts.nonEmpty &&
      !buffer.exists{case (st1,nxts1) =>
        st1 == renamedState && nxts1.sameElements(nexts)}){
      // Note: following duplicates later work
      // if(checkCompatible(map, renamedState, cpts, i, preCpts,otherArgs))
      buffer += ((renamedState, nexts))
    }
  }

  /** Exception showing renamedState is not representable using values in the
    * script. */
  private case class UnrepresentableException(renamedState: State) 
      extends Exception


  /** Cache of previous results of getRenamedStates. */
  private val mapCache = 
    new ShardedHashMap[(State, ProcessIdentity, ServerStates, List[State]), 
      Array[State]]

  /** Calculate all ways of remapping st (consistent with the servers) so
    * that: (1) its identity maps to pid; (2) other parameters are injectively
    * mapped either to a parameter in preCpts, but not the servers; or the
    * next fresh parameter.  
    * @return an Array of remapped states.  
    * @throw  UnrepresentableException if a renamed state is not representable 
    * in the script. */
  private def getRenamedStates(st: State, pid: ProcessIdentity,
    servers: ServerStates, preCpts: Array[State])
      : Array[State] = {
    val preCptsL = preCpts.toList
    mapCache.get(st, pid, servers, preCptsL) match{
      case Some(renamedStates) => renamedStates
      case None =>     // Profiler.count("getMaps: new") ~1.5%
        val (f,id) = pid; val map0 = servers.remappingMap
        val (otherArgs, nextArg) = Remapper.createMaps1(servers, preCpts)
        otherArgs(f) = removeFromList(otherArgs(f), id) 
        nextArg(f) = nextArg(f) max (id+1)
        val maps = Combiner.remapToId(map0, otherArgs, nextArg, st, id)
        // Create corresponding renamed States, and pair with maps
        val renamedStates = new Array[State](maps.length); var i = 0
        while(i < maps.length){
          val map = maps(i)
          val renamedState = Remapper.applyRemappingToState(map, st)
          if(!renamedState.representableInScript)
            throw UnrepresentableException(renamedState)
          renamedStates(i) = renamedState; i += 1
        }
        mapCache += (st, pid, servers, preCptsL) -> renamedStates
        renamedStates
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

}
