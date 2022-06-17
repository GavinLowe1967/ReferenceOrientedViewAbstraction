package ViewAbstraction.CombinerP 

import ViewAbstraction._
import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.ArrayBuffer
import ox.gavin.profiling.Profiler

/** Utility object to combine Views, Concretizations, etc.  Used within
  * Extendability and ConsistentStateFinder. */
object Combiner{
  /* remapToId (called from ConsistentStateFinder.getMaps)
   * |- remapState
   * 
   * areUnifiable (called from ConsistentStateFinder.checkCompatible and 
   * |             Extendability.compatibleWith)
   * |- remapRest
   *    |- remapSelectedStates
   */

  import Remapper.{show,extendMap}

  /** All ways of remapping st, consistent with map0, otherArgs and
    * nextArg, so that its identity maps to id.  Each parameter (f,id1) not in
    * the domain of map0 can be mapped to an element of otherArgs(f), or a
    * fresh value given by nextArg(f).  Note: map0 is mutated.  otherArgs and 
    * nextArg are mutated but backtracked.  Called from 
    * ConsistentStateFinder.getMaps.
    * Pre: extending map0 with so st.id -> id gives an injective map, and 
    * id is not in otherArgs(f).  Also otherArgs(f) is disjoint from ran(f). */
  def remapToId(map0: RemappingMap, otherArgs: OtherArgMap, nextArg: NextArgMap,
    /*cpts: Array[State], i: Int,*/ st: State, id: Identity)
      : ArrayBuffer[RemappingMap] = {
    assert(Remapper.isInjective(map0), show(map0))
    // Map identity of cpts(i) to id
    val f = st.family; val id0 = st.ids(0)
    // Check id not already in ran map0(f) other than at id0
    assert(map0(f).indices.forall(j => j == id0 || map0(f)(j) != id))
    assert(map0(f)(id0) < 0 || map0(f)(id0) == id, st)
    assert(!otherArgs(f).contains(id))
    for(f <- 0 until numTypes)
      require(otherArgs(f).forall(id1 => !map0(f).contains(id1)))
    map0(f)(id0) = id
    // Now remap the remaining components.
    remapState(map0, otherArgs, nextArg, st, 1)
  }

  /** All ways of remapping st.ids[from..), consistent with map0, otherArgs
    * and nextArg.  Each parameter (f,id) not in the domain of map0 can be
    * mapped to an element of otherArgs(f), or a fresh value given by
    * nextArg(f).  map0 is treated immutably, but cloned.  otherArgs and
    * nextArg are treated mutably, but all updates are backtracked. */
  @inline private[CombinerP] def remapState(
    map0: RemappingMap, otherArgs: OtherArgMap, nextArg: NextArgMap, 
    st: State, from: Int)
      : ArrayBuffer[RemappingMap] = {
    // require(Remapper.isInjective(map0), show(map0))
    // Elements of otherArgs should not appear in the range of the
    // corresponding part of map.
    // for(f <- 0 until numTypes)
    //   require(otherArgs(f).forall(id => !map0(f).contains(id)))
    val ids = st.ids; val typeMap = st.typeMap
    val result = ArrayBuffer[RemappingMap]()

    /* Extend map to remap st.ids[j..).  Add each resulting map to result.  */
    def rec(map: RemappingMap, j: Int): Unit = {
      if(j == ids.length) result += map // base case
      else{
        val f = typeMap(j); val id = ids(j) // remap (f,id)
        if(isDistinguished(id) || map(f)(id) >= 0)
          rec(map, j+1) // just move on; value of (f,id) fixed.
        else{
          // Case 1: map id to an element id1 of otherArgs(f)
          val newIds = otherArgs(f)
          for(id1 <- newIds){
            otherArgs(f) = newIds.filter(_ != id1) // temporary update (*)
            rec(extendMap(map, f, id, id1), j+1) // extend map and continue
          }
          otherArgs(f) = newIds                    // undo (*)

          // Case 2: map id to nextArg(f)
          val id1 = nextArg(f); nextArg(f) += 1   // temporary update (+)
          rec(extendMap(map, f, id, id1), j+1) // extend map and continue
          nextArg(f) -= 1                         // undo (+)
        }
      }
    }

    rec(map0, from); result
  }

  // IMPROVE NOTE: it isn't possible to use remapState directly in
  // remapSelectedStates, because if it necessary to carry the otherArgs and
  // nextArg over from one state to the next.  It could be done by passing a
  // "continuation" in to remapState, describing what to do with the resulting
  // map.

  /** All ways of remapping states except at index `exceptAt`, consistent with
    * map0, otherArgs and nextArg.  Each parameter (f,id) not in the domain of
    * map0 can be mapped to an element of otherArgs(f), or a fresh value given
    * by nextArg(f).  map0 is treated immutably, but cloned.  otherArgs and
    * nextArg are treated mutably, but all updates are backtracked. */
  private[CombinerP] 
  def remapSelectedStates(
    map0: RemappingMap, otherArgs: OtherArgMap, nextArg: NextArgMap,
    states: Array[State], exceptAt: Int) 
      : ArrayBuffer[RemappingMap] = {
    require(Remapper.isInjective(map0), show(map0))
    // println("remapSelectedStates: "+showRemappingMap(map0)+"; otherArgs = "+
    //   otherArgs.mkString(";")+"; nextArg = "+nextArg.mkString(";"))
    // Elements of otherArgs should not appear in the range of the
    // corresponding part of map.
    for(f <- 0 until numTypes)
      require(otherArgs(f).forall(id => !map0(f).contains(id)))
    val result = ArrayBuffer[RemappingMap]()

    /* Extend map to remap states(i).ids[j..), then states[i+1..).  Add each
     * resulting map to result.  */
    def rec(map: RemappingMap, i: Int, j: Int): Unit = {
      if(i == states.length) result += map // base case
      else if(exceptAt == i){  // skip this component
        assert(j == 0); rec(map, i+1, 0) }
      else{
        // IMPROVE: turn following into variables in outer scope; set when j = 0.
        val st = states(i); val ids = st.ids
        if(j == ids.length) rec(map, i+1, 0) // advance to next component
        else{
          val typeMap = st.typeMap
          val f = typeMap(j); val id = ids(j) // remap (f,id)
          if(isDistinguished(id) || map(f)(id) >= 0)
            rec(map, i, j+1) // just move on; value of (f,id) fixed.
          else{
            // Case 1: map id to an element id1 of otherArgs(f)
            val newIds = otherArgs(f)
            for(id1 <- newIds){
              otherArgs(f) = newIds.filter(_ != id1) // temporary update (*)
              rec(extendMap(map, f, id, id1), i, j+1) // extend map and continue
            }
            otherArgs(f) = newIds                    // undo (*)

            // Case 2: map id to nextArg(f)
            val id1 = nextArg(f); nextArg(f) += 1   // temporary update (+)
            rec(extendMap(map, f, id, id1), i, j+1) // extend map and continue
            nextArg(f) -= 1                         // undo (+)
          }
        }
      }
    } // end of rec
   
    // selector match{ 
    //   case Left(i) => rec(map0, i, 1); case Right(_) => rec(map0, 0, 0)
    // }
    rec(map0, 0, 0)
    result
  }

  /** Extend map0 to all elements of cpts except cpts(i), consistently with map0
    * and otherArgs, and then apply each such renaming to cpts.  
    * 
    * Pre: cpts.length > 1. */
  protected[CombinerP] def remapRest(
    map0: RemappingMap, otherArgs: OtherArgMap, cpts: Array[State], i: Int)
      : Array[Array[State]] = {
    assert(cpts.length > 1)
    if(false) assert({ val ids1 = cpts(i).ids; val typeMap = cpts(i).typeMap
      (0 until ids1.length).forall(j => 
        ids1(j) < 0 || map0(typeMap(j))(ids1(j)) >= 0
      )}, 
      "\nmap = "+show(map0)+"undefined on cpts(i) = "+cpts(i) )
    // But we potentialy need this property within applyRenaming, below.
    val nextArg = new Array[Int](numTypes)
    var f = 0
    while(f < numFamilies){
      // Set nextArg(f) > ran map0(f), otherArgs(f)
      var i = 0; var maxId = nextArg(f)
      while(i < map0(f).length){ maxId = maxId max (map0(f)(i)+1); i += 1 }
      var oa = otherArgs(f)
      while(oa.nonEmpty){ maxId = maxId max (oa.head+1); oa = oa.tail }
      nextArg(f) = maxId; f += 1
    }
    val maps = remapSelectedStates(map0, otherArgs, nextArg, cpts, i)
    var result = new Array[Array[State]](maps.length); var j = 0
    while(j < maps.length){
      result(j) = Remapper.applyRemapping(maps(j), cpts); j += 1
    }
    result
    // for(map <- maps) yield Remapper.applyRemapping(map, cpts)
  }

  /** Is there some renaming of cpts1, excluding cpts1(i) that agrees with cpts2
    * on common components?  The remapping must be compatible with map and
    * otherArgs.  Both map and otherArgs are guaranteed not to change.  */
  def areUnifiable(cpts1: Array[State], cpts2: Array[State], 
    map: RemappingMap, i: Int, otherArgs: OtherArgMap)
      : Boolean = {              
    Profiler.count("areUnifiable")
    if(cpts1.length == 1){ assert(i == 0); true }
    else{
      //var otherArgs1: OtherArgMap = otherArgs // null
      // All renamings of cpts1.
      val remappedCptss = remapRest(map, otherArgs, cpts1, i)
      // Test if any agrees with cpts2 on common components.
      remappedCptss.exists(StateArray.agreeOnCommonComponents(_, cpts2, i))
    }
  }



}
