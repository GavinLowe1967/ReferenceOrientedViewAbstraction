package ViewAbstraction

import scala.collection.mutable.ArrayBuffer

/** Tester for Unification. */
object UnificationTest 
    extends Unification.Tester with EffectOnUnification.Tester{
  import TestStates._
  import RemapperP.Remapper.{show,newRemappingMap}
  import RemapperP.RemapperTest.{emptyMap,checkMap}
  import Unification.{unify,CombineResult,remapToJoin}
  import EffectOnUnification.{combine,MatchingTuple}

  /** Test of unify. */
  private def unifyTest = {
    var map = newRemappingMap
    assert(unify(map, aNode(0,-1), aNode(0,1)) == null) // 7[0](N0,Null), 7[0](N0,N1)
    assert(unify(map, aNode(1,-1), aNode(0,1)) == null) // 7[0](N1,Null), 7[0](N0,N1)

    var map1 = unify(map, aNode(0,-1), aNode(1,-1)) // 7[0](N0,Null), 7[0](N1,Null),
    // give N1->N0
    assert(map1 != null && checkMap(map1(0), 1, 0) && emptyMap(map1(1)))

    // 7[0](N0,Null), 7[0](N1,Null), but fix N1 -> N2, so unification should fail
    map = newRemappingMap; map(0)(1) = 2; 
    assert(unify(map, aNode(0,-1), aNode(1,-1)) == null)

    // 7[0](N0,N1), 7[0](N1,N0)
    map = newRemappingMap; map1 = unify(map, aNode(0,1), aNode(1,0)) 
    // N0 -> N1, N1 -> N0
    assert(map1 != null && map1(0)(1) == 0 && map1(0)(0) == 1 &&
      map1(0).indices.forall(i => i<=1 || map1(0)(i) == -1) && emptyMap(map1(1)))

    // 7[0](N0,N1), 7[0](N1,N2) fixing N1 -> N0; adds N2 -> N1
    map = newRemappingMap; map(0)(1) = 0; map1 = unify(map, aNode(0,1), aNode(1,2))
    assert(map1 != null && map1(0)(1) == 0 && map1(0)(2) == 1 &&
      map1(0).indices.forall(i => i == 1 || i ==2 || map1(0)(i) == -1) &&
      emptyMap(map1(1)))
  }

  /** Test of Unification.allUnifs. */
  private def allUnifsTest = {
    println("== allUnifsTest ==")
    def showBuffer(buff: AllUnifsResult) =
      buff.map{ case (map, us) => show(map)+"; "+us }.mkString("\n")

    def test1 = {
      val buffer = 
        allUnifs(newRemappingMap, Array(aNode(N0,N1)), Array(aNode(N2,N3)))
      // println("\n"+showBuffer(buffer))
      // One result without unification: can't unify principals.
      assert(buffer.length == 1)
      assert(buffer.forall{case (map, unifs) => 
        map.forall(emptyMap) && unifs.isEmpty //  ||
        // checkMap(map(0), List((2,0), (3,1))) && emptyMap(map(1)) &&
        //   unifs == List((0,0))
      })
    }

    def test2 = {
      //println("test2")
      val buffer = 
        allUnifs(newRemappingMap, Array(aNode(N0,N1), aNode(N1,N2)), 
          Array(aNode(N2,N3), aNode(N3,N4)))
      // println("\n"+showBuffer(buffer))
      assert(buffer.length == 4)
      assert(buffer.forall{case (map, unifs) => 
        emptyMap(map(1)) && (
          // unify both -- no, can't unify principals
          // checkMap(map(0), List((2,0), (3,1), (4,2))) && 
            // unifs == List((1,1), (0,0)) ||
            // N2 -> N1, N3 -> N2
            checkMap(map(0), List((2,1),(3,2))) && unifs == List((0,1)) ||
            // N3 -> N0, N4 -> N1
            checkMap(map(0), List((3,0),(4,1))) && unifs == List((1,0)) ||
            // N3 -> N1, N4 -> N2
            checkMap(map(0), List((3,1),(4,2))) && unifs == List((1,1)) ||
            // no unification
            emptyMap(map(0)) && unifs.isEmpty
        )})
    }

    def test3 = {
      val buffer = 
        allUnifs(newRemappingMap, Array(initNodeSt(T0,N0), aNode(N0,N1)), 
          Array(unlock(T0), aNode(N2,N3)))
      // println("\n"+showBuffer(buffer))
      // One result without unification: can't unify principals.
      assert(buffer.length == 2)
      assert(buffer.forall{case (map, unifs) => 
        map.forall(emptyMap) && unifs.isEmpty  ||
        checkMap(map(0), List((2,0), (3,1))) && emptyMap(map(1)) &&
          unifs == List((1,1))
      })
    }

    def test4 = {
      // println("test4")
      val buffer = 
        allUnifs(newRemappingMap, 
          Array(initNodeSt(T0,N0), aNode(N0,N1), aNode(N1,N2)),
          Array(unlock(T0), aNode(N2,N3), aNode(N3,N4)))
      // println("\n"+showBuffer(buffer))
      assert(buffer.length == 5)
      assert(buffer.forall{case (map, unifs) => 
        emptyMap(map(1)) && (
          // unify both nodes
          checkMap(map(0), List((2,0), (3,1), (4,2))) && 
            unifs == List((2,2), (1,1)) ||
            // N2 -> N1, N3 -> N2
            checkMap(map(0), List((2,1),(3,2))) && unifs == List((1,2)) ||
            // N3 -> N0, N4 -> N1
            checkMap(map(0), List((3,0),(4,1))) && unifs == List((2,1)) ||
            // N3 -> N1, N4 -> N2
            checkMap(map(0), List((3,1),(4,2))) && unifs == List((2,2)) ||
            // no unification
            emptyMap(map(0)) && unifs.isEmpty
        )})
    }

    test1; test2; test3; test4
  }

  /** Test of Unification.combine. */
  private def combineTest = {
    println("== combineTest ==")
    def showBuffer(buff: CombineResult) =
      buff.map{ case (map, states, us) => 
        RemapperP.Remapper.show(map)+"; "+StateArray.show(states)+"; "+us 
      }.mkString("\n")

    def test1 = {
      println("=test1=")
      val pre = new Concretization(servers0, 
        Array(/*initNodeSt*/getDatumSt(T0,N0,N1), aNode(N0,N2), aNode(N1,Null)) )
      val post = new Concretization(servers2, 
        Array(unlock(T0), bNode(N0,N1), aNode(N1,Null)))
      val cv = new ComponentView(servers0, Array(aNode(N0,N1), cNode(N1,Null)))
      // val cv = new ComponentView(servers0, Array(aNode(N2,N3)))
      // servers0 contains no ids, servers2 contains T0, N0
      val (buffer,_) = combine(pre, post, cv /*, List()*/) // , true
      // println(showBuffer(buffer))
      // Unifying, N0 -> N0, N1 -> N1
      assert(buffer.exists{case (map, states, unifs) =>
        unifs == List((0,1)) && 
        states.sameElements(Array(aNode(N0,N2), cNode(N2,Null)))
      })
      // No unification
      assert(buffer.exists{case (map, states, unifs) =>
        unifs.isEmpty && states.sameElements(Array(aNode(N3,N4), cNode(N4,Null)))
      })
      assert(buffer.length == 2)

      // effectOnChangedServersCache.clear
      //println("=test1a=")
      cv.clearInduced
      val (buffer2,_) = combine(pre, post, cv /*, List()*/) // , false
      // Unifying, N0 -> N0, N1 -> N1
      //println(showBuffer(buffer2))
      assert(buffer2.exists{case (map, states, unifs) =>
        unifs == List((0,1)) && 
        states.sameElements(Array(aNode(N0,N2), cNode(N2,Null)))
      })
      // No unification, N0 -> N3, N1 -> N4
      assert(buffer2.exists{case (map, states, unifs) =>
        unifs.isEmpty && states.sameElements(Array(aNode(N3,N4), cNode(N4,Null)))
      })
      assert(buffer2.length == 2)
    }

    def test2 = {
      //println("\n=test2=")
      // effectOnChangedServersCache.clear
      val pre = new Concretization(servers0, 
        Array(getDatumSt(T0,N0,N1), aNode(N0,N2), bNode(N1,N3)) )
      val post = 
        new Concretization(servers2, 
          Array(setTopB(T0,N0), bNode(N0,N1), bNode(N1,N3)) )
      val cv = new ComponentView(servers0, Array(aNode(N0,N1), cNode(N1,Null)))
      val (buffer,_) = combine(pre, post, cv /*, List()*/) // , false
      // Note, N2 in pre is ignored as it doesn't unify 
      // println(showBuffer(buffer))
      assert(buffer.length == 2)
      // Unifying N2 -> N0, N3 -> N2
      assert(buffer.exists{case (map, states, unifs) =>
        unifs == List((0,1)) && 
        states.sameElements(Array(aNode(N0,N2), cNode(N2,Null)))
      })
      // No unification; N0 -> N4, N1 -> N5
      assert(buffer.exists{case (map, states, unifs) =>
        unifs.isEmpty && states.sameElements(Array(aNode(N4,N5), cNode(N5,Null)))
      })
    }

    def test3 = {
      //println("=test3=")
      val pre = new Concretization(servers1, 
        Array(getDatumSt(T0,N0,N1), aNode(N0,N2), bNode(N1,N3)) )
      val post = 
        new Concretization(servers2, 
          Array(setTopB(T0,N0), bNode(N0,N1), bNode(N1,N3)) )
      val cv = new ComponentView(servers1, 
        Array(getDatumSt(T0,N0,Null), aNode(N0,N1)))
      val (buffer,_) = combine(pre, post, cv /*, List()*/) // , false
      // servers1 contains T0, and the T0 components in pre and cv can't be 
      // unified.
      assert(buffer.isEmpty)
    }

    def test4 = {
      //println("=test4=")
      // val pre = new Concretization(servers1, 
      //   Array(getDatumSt(T0,N0,N2), aNode(N0,N1), bNode(N2,N3)) )
      // val post = 
      //   new Concretization(servers2, 
      //     Array(setTopB(T0,N0), bNode(N0,N2), bNode(N2,N3)) )
      val pre = new Concretization(servers1, 
        Array(getDatumSt(T0,N0,N1), aNode(N0,N2), bNode(N1,N3)) )
      val post = 
        new Concretization(servers2, 
          Array(setTopB(T0,N0), bNode(N0,N1), bNode(N1,N3)) )
      // servers2 contains N0 and T0
      val cv = new ComponentView(servers1, 
        Array(getDatumSt(T1,N0,N2), aNode(N0,N1), cNode(N2,N3)))
      val (buffer,_) = combine(pre, post, cv /*, List()*/) // , false
      // println("\n"+showBuffer(buffer))
      assert(buffer.forall{case (map, states, unifs) =>
        unifs == List((1,1)) && ( 
          // N0 -> N0, N1 -> N2, T1 -> T1, N2 -> fresh (can't map to N1),
          // N3 -> N1 or fresh
          states.sameElements( // N3 -> N1
            Array(getDatumSt(T1,N0,N4), aNode(N0,N2), cNode(N4,N1))) ||
            states.sameElements( // both fresh
              Array(getDatumSt(T1,N0,N4), aNode(N0,N2), cNode(N4,N5)))
        ) ||
        unifs.isEmpty && (
          // T1 -> T1; N0, N2 -> fresh values; N1, N3 -> N0 (from servers2) or
          // fresh values.
          states.sameElements(
            Array(getDatumSt(T1,N4,N5), aNode(N4,N0), cNode(N5,N6))) ||
            states.sameElements(
              Array(getDatumSt(T1,N4,N5), aNode(N4,N6), cNode(N5,N0))) ||
            states.sameElements(
              Array(getDatumSt(T1,N4,N5), aNode(N4,N6), cNode(N5,N7))) 
        )
        //   states.sameElements( // N0 -> N0
        //     Array(getDatumSt(T1,N0,N1), aNode(N0,N2), cNode(N1,N3))) ||
        //     states.sameElements( // N2 -> N0
        //       Array(getDatumSt(T1,N1,N0), aNode(N1,N2), cNode(N0,N3))) ||
        //     states.sameElements( // N1 -> N0
        //       Array(getDatumSt(T1,N1,N2), aNode(N1,N0), cNode(N2,N3))) ||
        //     states.sameElements( // N3 -> N0
        //       Array(getDatumSt(T1,N1,N2), aNode(N1,N3), cNode(N2,N0))) ||
        //     states.sameElements( // all fresh
        //       Array(getDatumSt(T1,N1,N2), aNode(N1,N3), cNode(N2,N4)))
        // )
      })
    }

    def test5 = {
      //println("\n=test5=")
      val pre = new Concretization(servers1, 
        Array(initNodeSt(T0,Null), initNode(N0)))
      val post = new Concretization(servers1, 
        Array(setTopB(T0,N0), bNode(N0,Null)))
      val cv = new ComponentView(servers1, Array(initNodeSt(T0,Null)))
      val (buffer,_) = combine(pre, post, cv /*, List()*/) // , false
// FIXME: test here
      //println(showBuffer(buffer))
    }

    test1; test2; test3; test4; test5

  }

  /** Test of remapToJoin. */
  private def remapToJoinTest = {
    println("== remapToJoinTest ==")
    def test1 = {
      //println("= test1 =")
      val result = 
        remapToJoin(servers2, pushSt(T0,N1), Array(pushSt(T1,N2)), aNode(N1,N3))
      // println(result.mkString(", "))
      // N1 -> N1, N3 -> N2|N3
      assert(result.contains(aNode(N1,N2)) && result.contains(aNode(N1,N3)) &&
        result.length == 2)
    }

    def test2 = { 
      //println("= test2 =")
      val result = 
        remapToJoin(servers2, popSt(T0,N0,N1), Array(popSt(T1,N2,N3)), aNode(N1,N2))
      //println(result.mkString(", "))
      // N1 -> N1, N3 -> N2|N3|N4
      assert(result.contains(aNode(N1,N2)) && result.contains(aNode(N1,N3)) &&
        result.contains(aNode(N1,N4)) && result.length == 3)
    }

    def test3 = { 
      //println("= test3 =")
      val result = 
        remapToJoin(servers2, popSt(T0,N0,N1), Array(popSt(T1,N0,N2)), aNode(N1,N2))
      //println(result.mkString(", "))
      // N1 -> N1, N3 -> N2|N3
      assert(result.contains(aNode(N1,N2)) && result.contains(aNode(N1,N3)) &&
        result.length == 2)
    }

    singleRef = true
    test1; test2; test3
    singleRef = false
  }

  /** Test of reampToCreateCrossRefs. */
  private def remapToCreateCrossRefsTest = {
    println("==remapToCreateCrossRefsTest==")

    def rTCCR(cpts1: Array[State], cpts2: Array[State], map: RemappingMap) =
      remapToCreateCrossRefs(cpts1, cpts2, map)

    def showResult(result: ArrayBuffer[(RemappingMap, List[MatchingTuple])]) = 
      for((map, tuples) <- result) println(show(map)+": "+tuples)

    val cpts1 = Array(aNode(N0,N1),bNode(N1,N2)) 
    val cpts1X = Array(aNode(N0,N1),bNode(N1,Null))
    val cpts2 = Array(bNode(N0,N1),cNode(N1,N2))
    val cpts2X = Array(bNode(N0,N1),cNode(N1,Null))

    def test1 = {
      val map0 = newRemappingMap
      val result = rTCCR(cpts1, cpts2, map0)
      // (N0 -> N2 xor N1 -> N2) or neither; (N2 -> N0 xor N2 -> N1) or neither
      // showResult(result)
      assert(result.length == 9, showResult(result))
      val result2 = rTCCR(cpts1X, cpts2, map0)
      // (N2 -> N0 xor N2 -> N1) or neither
      assert(result2.length == 3, showResult(result2))
      val result3 = rTCCR(cpts1, cpts2X, map0)
      // (N0 -> N2 xor N1 -> N2) or neither
      assert(result3.length == 3, showResult(result3))
      val result4 = rTCCR(cpts1X, cpts2X, map0)
      // No links; identity map
      assert(result4.length == 1, showResult(result4))
    }

    def test2 = {
      val map0 = newRemappingMap; map0(0)(0) = 0
      val result = rTCCR(cpts1, cpts2, map0)
      // N2 -> N1 or not; N1 -> N2 or not
      assert(result.length == 4, showResult(result))

      val result2 = rTCCR(cpts1X, cpts2, map0)
      // N2 -> N1 or not
      assert(result2.length == 2, showResult(result2))

      val result3 = rTCCR(cpts1, cpts2X, map0)
      // N1 -> N2 or not
      assert(result3.length == 2, showResult(result3))

      val result4 = rTCCR(cpts1X, cpts2X, map0)
      // No links; identity map
      assert(result4.length == 1, showResult(result4))
    }

    def test3 = {
      val cpts1 = Array(getDatumSt(T0,N0,N1), aNode(N0,N2))
      val cpts2 = Array(bNode(N0,N1),cNode(N1,Null))
      val map0 = newRemappingMap
      val result = rTCCR(cpts1, cpts2, map0)
      // N0 -> N1, N2 or neither; N1 -> N1, N2 or neither; but injective
      assert(result.length == 7, showResult(result))

      val cpts1X = Array(getDatumSt(T0,N0,N1), aNode(N1,N2))
      val result2 = rTCCR(cpts1X, cpts2, map0)
      assert(result2.length == 7, showResult(result2))
      // N0 -> N0, N2 or neither; N1 -> N0, N2 or neither; but injective
    }

    test1; test2; test3
  }


  /** Main test function. */
  def test = {
    println("===UnificationTest===")
    unifyTest; allUnifsTest; combineTest; remapToJoinTest; remapToCreateCrossRefsTest
  }
}
