package ViewAbstraction.CombinerP 

import ViewAbstraction._
import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.ArrayBuffer

/** Utility object to combine Views, Concretizations, etc. */

object Combiner{
  import Remapper.{RemappingMap,OtherArgMap,NextArgMap,show}

  /** All ways of remapping certain states of states, consistent with map0,
    * otherArgs and nextArg.  If selector = Left(i) then just the non-identity
    * parameters of states(i) are renamed.  If selector = Right(i) then every
    * state except states(i) is renamed.  Each parameter (f,id) not in the
    * domain of map0 can be mapped to an element of otherArgs(f), or a fresh
    * value given by nextArg(f).  map0 is treated immutably, but cloned.
    * otherArgs and nextArg are treated mutably, but all updates are
    * backtracked. */
  private[CombinerP] 
  def remapSelectedStates(
    map0: RemappingMap, otherArgs: OtherArgMap, nextArg: NextArgMap,
    states: Array[State], selector: Either[Int, Int]) 
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
      if(i == states.length || selector == Left(i-1)) 
        result += map // base case
      else if(selector == Right(i)){  // skip this component
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
              rec(Remapper.extendMap(map, f, id, id1), i, j+1) // extend map and continue
            }
            otherArgs(f) = newIds                    // undo (*)

            // Case 2: map id to nextArg(f)
            val id1 = nextArg(f); nextArg(f) += 1   // temporary update (+)
            rec(Remapper.extendMap(map, f, id, id1), i, j+1) // extend map and continue
            nextArg(f) -= 1                         // undo (+)
          }
        }
      }
    } // end of rec
   
    selector match{ 
      case Left(i) => rec(map0, i, 1); case Right(_) => rec(map0, 0, 0)
    }
    result
  }

  /** All ways of remapping cpts(i), consistent with map0, otherArgs and
    * nextArg, so that its identity maps to id.  Each parameter (f,id1) not in
    * the domain of map0 can be mapped to an element of otherArgs(f), or a
    * fresh value given by nextArg(f). 
    * Pre: extending map0 with so cpts(i).id -> id gives an injective map, and 
    * id is not in otherArgs(f).  Also otherArgs(f) is disjoint from ran(f). */
  def remapToId(map0: RemappingMap, otherArgs: OtherArgMap, nextArg: NextArgMap,
    cpts: Array[State], i: Int, id: Identity)
      : ArrayBuffer[RemappingMap] = {
    assert(Remapper.isInjective(map0), show(map0))
    // Map identity of cpts(i) to id
    val st = cpts(i); val f = st.family; val id0 = st.ids(0)
    // Check id not already in ran map0(f) other than at id0
    assert(map0(f).indices.forall(j => j == id0 || map0(f)(j) != id))
    assert(map0(f)(id0) < 0 || map0(f)(id0) == id,
      s"cpts = "+cpts.mkString("[",";","]")+s"; f = $f; id0 = $id0 -> "+
        map0(f)(id0)+s"; id = $id")
    assert(!otherArgs(f).contains(id))
    for(f <- 0 until numTypes)
      require(otherArgs(f).forall(id1 => !map0(f).contains(id1)))
    // println(s"remapToId($st): "+showRemappingMap(map0)+"; otherArgs = "+
    //   otherArgs.mkString(";")+"; nextArg = "+nextArg.mkString(",")+";"+
    //   (id0,id))
    map0(f)(id0) = id
    // Now remap the remaining components.
    remapSelectedStates(map0, otherArgs, nextArg, cpts, Left(i))
  }


  /** Extend map0 to all elements of cpts except cpts(i), consistently with map0
    * and otherArgs, and then apply each such renaming to cpts.  
    * 
    * Pre: cpts.length > 1. */
  protected[CombinerP] def remapRest(
    map0: RemappingMap, otherArgs: OtherArgMap, cpts: Array[State], i: Int)
      : ArrayBuffer[Array[State]] = {
    assert(cpts.length > 1)
    // The following tests fail.
    // If coming via Checker.compatibleWith, parameters of cpts(i) are in the
    // range of map0; but not if coming via System.consistentStates.
    // assert({ val ids1 = cpts(i).ids; val typeMap = cpts(i).typeMap
    //   (0 until ids1.length).forall(j => 
    //     ids1(j) < 0 || map0(typeMap(j)).contains(ids1(j))
    //   )}, 
    //   "\nmap = "+show(map0)+"undefined on cpts(i) = "+cpts(i) )
    // If coming via System.consistentStates, cpts(i) are in the domain of map0;
    // but not if coming via Checker.compatibleWith.
    assert({ val ids1 = cpts(i).ids; val typeMap = cpts(i).typeMap
      (0 until ids1.length).forall(j => 
        ids1(j) < 0 || map0(typeMap(j))(ids1(j)) >= 0
      )}, 
      "\nmap = "+show(map0)+"undefined on cpts(i) = "+cpts(i) )
    // But we potentialy need this property within applyRenaming, below.
    val nextArg = new Array[Int](numTypes)
    for(f <- 0 until numFamilies){
      for(id <- map0(f)) nextArg(f) = nextArg(f) max (id+1)
      if(otherArgs(f).nonEmpty) nextArg(f) = nextArg(f) max (otherArgs(f).max+1)
    }
    val maps = remapSelectedStates(map0, otherArgs, nextArg, cpts, Right(i))
    for(map <- maps) yield Remapper.applyRemapping(map, cpts)
  }

  /** Is there some renaming of cpts1, excluding cpts1(i) that agrees with cpts2
    * on common components?  The remapping must be compatible with map and
    * otherArgs.  Both map and otherArgs are guaranteed not to change.  */
  def areUnifiable(cpts1: Array[State], cpts2: Array[State], 
    map: RemappingMap, i: Int, otherArgs: OtherArgMap)
      : Boolean = {              
    if(cpts1.length == 1){ assert(i == 0); true }
    else{
      //var otherArgs1: OtherArgMap = otherArgs // null
      // All renamings of cpts1.
      val remappedCptss = remapRest(map, otherArgs, cpts1, i)
      // Test if any agrees with cpts2 on common components.
      remappedCptss.exists(View.agreeOnCommonComponents(_, cpts2, i))
    }
  }



}
