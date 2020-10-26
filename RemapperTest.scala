package ViewAbstraction.RemapperP 

import ViewAbstraction._
import scala.collection.mutable.ArrayBuffer

/** Testing functions on Remapper.  These assume that test3.csp is loaded. */
object RemapperTest{
  import RemapperP.Remapper._
  import TestStates._
  import View.showStates

  // ======== Helper functions

  /** Check that map is the mapping {i -> j}. */
  private def checkMap(map: Array[Int], i: Int, j: Int) =
    map(i) == j && map.indices.forall(i1 => i1 == i || map(i1) == -1)

  /** Check that map is the mapping {(i,j) | (i,j) <- pairs}. */
  private def checkMap(map: Array[Int], pairs: List[(Int,Int)]) =
    map.indices.forall(i => pairs.filter(_._1 == i) match{
      case List() => map(i) == -1
      case List((i1,j)) => map(i) == j
    })

  private def emptyMap(map: Array[Int]) = map.forall(_ == -1)

  // ======== Now the tests

  /** Test on createCombiningMaps. */
  private def createCombiningMapsTest = {
    val (map, otherArgs, nextArgs) = createCombiningMaps(servers1, components1)
    // [21[-1](T0) || 22[-1](Null) || 23[-1]()] || [12[1](T0,N0) || 7[0](N0,N1)]
    assert(map(0).forall(_ == -1) && checkMap(map(1), 0, 0) )
    assert(otherArgs(0).sorted == List(0,1) && otherArgs(1).sorted == List())
    assert(nextArgs(0) == 2 && nextArgs(1) == 1)
  }

  private def createMaps1Test = {
    // [21[-1](T0) || 22[-1](Null) || 23[-1]()] || [12[1](T0,N0) || 7[0](N0,N1)]
    val (others, nexts) = createMaps1(servers1, components1)
    assert(others(0).sorted == List(0,1) && others(1).sorted == List())
    assert(nexts(0)==2 && nexts(1)==1)

    // [21[-1](T0) || 22[-1](N0) || 23[-1]()] || 6[0](N1)
    val (others2, nexts2) = createMaps1(servers2, Array(initNode(N1)))
    assert(others2(0) == List(1) && others2(1) == List() &&
      nexts2(0) == 2 && nexts2(1) == 1)
  }

  private def unifyTest = {
    var map = newRemappingMap
    assert(! unify(map, aNode(0,-1), aNode(0,1))) // 7[0](N0,Null), 7[0](N0,N1)
    assert(! unify(map, aNode(1,-1), aNode(0,1))) // 7[0](N1,Null), 7[0](N0,N1)

    var ok = unify(map, aNode(0,-1), aNode(1,-1)) // 7[0](N0,Null), 7[0](N1,Null),
    // give N1->N0
    assert(ok && checkMap(map(0), 1, 0) && map(1).forall(_ == -1))

    // 7[0](N0,Null), 7[0](N1,Null), but fix N1 -> N2, so unification should fail
    map = newRemappingMap; map(0)(1) = 2; 
    assert(!unify(map, aNode(0,-1), aNode(1,-1)))

    // 7[0](N0,N1), 7[0](N1,N0)
    map = newRemappingMap; ok = unify(map, aNode(0,1), aNode(1,0)) 
    // N0 -> N1, N1 -> N0
    assert(ok && map(0)(1) == 0 && map(0)(0) == 1 &&
      map(0).indices.forall(i => i<=1 || map(0)(i) == -1) && map(1).forall(_ == -1))

    // 7[0](N0,N1), 7[0](N1,N2) fixing N1 -> N0; adds N2 -> N1
    map = newRemappingMap; map(0)(1) = 0; ok = unify(map, aNode(0,1), aNode(1,2))
    assert(ok && map(0)(1) == 0 && map(0)(2) == 1 &&
      map(0).indices.forall(i => i == 1 || i ==2 || map(0)(i) == -1) &&
      map(1).forall(_ == -1))
  }

  private def combine1Test = {
    def test1 = { // 6[0](N0), 6[0](N1), allowing N1 -> N0
      val buff = combine1(newRemappingMap, Array(1,0), Array(List(0), List()),
        Array(initNode(N0)), Array(initNode(N1)))
      assert(buff.length == 2)
      assert(buff.exists{case(map1,unifs) => // mapping N1 -> N0 with unification
        checkMap(map1(0), 1, 0) && map1(1).forall(_ == -1) && unifs == List((0,0))
      })
      assert(buff.exists{case(map1,unifs) => // mapping N1 -> N1
        checkMap(map1(0), 1, 1) && map1(1).forall(_ == -1) && unifs == List()
      })
    }
    def test2 = { // Thread(T0) and InitNode(N0/N1)
      val buff = combine1(newRemappingMap, Array(1,1), Array(List(0), List()),
        Array(initSt(T0), initNode(N0)), Array(initSt(T0), initNode(N1)))
      // println(buff.map{case(map1,unifs) => show(map1)+"; "+unifs}.mkString("\n"))
      assert(buff.length == 2)
      assert(buff.exists{case(map1,unifs) => // N1 -> N0, with unification, T0 -> T1
        checkMap(map1(0), 1, 0) && checkMap(map1(1), 0, 1) && unifs == List((1,1))
      })
      assert(buff.exists{case(map1,unifs) => // N1 -> N1, no unification, T0 -> T1
        checkMap(map1(0), 1, 1) && checkMap(map1(1), 0, 1) && unifs == List()
      })
    }
    def test3 = { // Thread(T0) and InitNode(N0/N1)
      val buff = combine1(newRemappingMap, Array(1,1), Array(List(0), List(0)),
        Array(initSt(T0), initNode(N0)), Array(initSt(T0), initNode(N1)))
      assert(buff.length == 4)
      assert(buff.forall{case(map1,unifs) =>
        // N1 -> N0 with unification; or N1 -> N1 without unification
        ( checkMap(map1(0), 1, 0) && unifs.contains((1,1)) ||
          checkMap(map1(0), 1, 1) && !unifs.contains((1,1)) ) &&
        // T0 -> T0 with unification; or T0 -> T1 without unification
        ( checkMap(map1(1), 0, 0) && unifs.contains((0,0)) ||
          checkMap(map1(1), 0, 1) && !unifs.contains((0,0)) ) &&
        unifs.forall(u => u == (0,0) || u == (1,1))
      })
    }
    def test4 = { // 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,N1) || 7[0](N1,N2)
      val buff = combine1(newRemappingMap, Array(2,1), Array(List(0), List(0)),
        components1, nodes)
      assert(buff.length == 3)
      assert(buff.exists{case(map1,unifs) => // N0 -> N0, N1 -> N1 with unif, N2 -> N2
        checkMap(map1(0), List((0,0), (1,1), (2,2))) &&
        map1(1).forall(_ == -1) && unifs == List((1,0))
      })
      assert(buff.exists{case(map1,unifs) => // N1 -> N0, N2 -> N1 with unif; N0 -> N2
        checkMap(map1(0), List((1,0), (2,1), (0,2))) &&
        emptyMap(map1(1)) && unifs == List((1,1))
      })
      assert(buff.exists{case(map1,unifs) => // N0 -> N2, N1 -> N3, N2 -> N4, no unifs
        checkMap(map1(0), List((0,2), (1,3), (2,4))) &&
        emptyMap(map1(1)) && unifs.isEmpty
      })
    }
    def test5 = { 
      // 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,N1) || 7[0](N1,N2) with N1 -> N0
      val map = newRemappingMap; map(0)(1) = 0
      val buff = combine1(map, Array(2,1), Array(List(), List(0)), 
        components1, nodes)
      // println(buff.map{case(map1,unifs) => show(map1)+"; "+unifs}.mkString("\n"))
      assert(buff.length == 1) // just second case from previous test
      assert{val (map1,unifs) = buff.head; // N1 -> N0, N2 -> N1 with unif; N0 -> N2
        checkMap(map1(0), List((1,0), (2,1), (0,2))) &&
        emptyMap(map1(1)) && unifs == List((1,1)) }
      // ......................
    }
    test1; test2; test3; test4; test5
  } // end of combine1Test

  private def combineTest = {
    def test1 = { // 6[0](N0), 6[0](N1)
      val v1 = new Concretization(servers1, Array(initNode(N0)))
      val v2 = new ComponentView(servers1, initNode(N1), Array())
      val buff = combine(v1, v2)
      assert(buff.length == 2)
      // N1 -> N0 with unif; or N1 -> N1
      assert(buff.forall{ case(Array(st), unifs) => 
        st == initNode(N0) && unifs == List((0,0)) || 
        st == initNode(N1) && unifs.isEmpty
      })
    }
    def test2 = { // 6[0](N0), 6[0](N0)
      val v1 = new Concretization(servers1, Array(initNode(N0)))
      val v2 = new ComponentView(servers1, initNode(N0), Array())
      val buff = combine(v1, v2)
      assert(buff.length == 2)
      // N0 -> N0 with unif; or N0 -> N1
      assert(buff.forall{ case(Array(st), unifs) => 
        st == initNode(N0) && unifs == List((0,0)) || 
        st == initNode(N1) && unifs.isEmpty
      })
    }
    def test3 = { // Thread with ref to A-node, and A-node
      val v1 = new Concretization(servers1, Array(pushSt(T0,N0), aNode(0,-1)))
      val v2 = new ComponentView(servers1, aNode(0,-1), Array())
      val buff = combine(v1, v2)
      assert(buff.length == 2)
      // N0 -> N0 with unif; or N0 -> N1
      assert(buff.forall{ case(Array(st), unifs) => 
        st == aNode(0,-1) && unifs == List((1,0)) || 
        st == aNode(1,-1) && unifs.isEmpty })
    }
    def test4 = { // Thread with ref to A-node with non-null next, and A-node
                  // with null next: 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,Null)
      val v1 = new Concretization(servers1, Array(pushSt(T0,N0), aNode(0,1)))
      val v2 = new ComponentView(servers1, aNode(0,-1), Array())
      val buff = combine(v1, v2)
      // N0 -> N1 or N0 -> N2
      assert(buff.length == 2)
      assert(buff.forall{ case(Array(st), unifs) => 
        (st == aNode(1,-1) || st == aNode(2,-1)) && unifs.isEmpty })
    }
    def test5 = { // 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,N1) || 7[0](N1,N2)
      val v1 = new Concretization(servers1, Array(pushSt(T0,N0), aNode(0,1)))
      val v2 = new ComponentView(servers1, aNode(0,1), Array(aNode(1,2)))
      val buff = combine(v1, v2)
      // 7[0](N0,N1) || 7[0](N1,N2); List((1,0))
      // 7[0](N2,N0) || 7[0](N0,N1); List((1,1))
      // 7[0](N1,N2) || 7[0](N2,N3); List().  
      // 7[0](N2,N1) || 7[0](N1,N3); List()
      // 7[0](N2,N3) || 7[0](N3,N4); List()
      assert(buff.length == 5)
      assert(buff.forall{ case(Array(st1, st2), unifs) =>
        st1 == aNode(0,1) && st2 == aNode(1,2) && unifs == List((1,0)) || // N0 -> N0
        st1 == aNode(2,0) && st2 == aNode(0,1) && unifs == List((1,1)) || // N1 -> N0
        st1 == aNode(1,2) && st2 == aNode(2,3) && unifs.isEmpty ||  // N0 -> N1
        st1 == aNode(2,1) && st2 == aNode(1,3) && unifs.isEmpty|| // N1 -> N1
        st1 == aNode(2,3) && st2 == aNode(3,4) && unifs.isEmpty // distinct nodes
      })
    }
    def test6 = {// 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,N1) || 7[0](N1,N2)
                 // with Top = N0
      val v1 = new Concretization(servers2, Array(pushSt(T0,N0), aNode(0,1)))
      val v2 = new ComponentView(servers2, aNode(0,1), Array(aNode(1,2)))
      // println(v1.toString+"\n"+v2)
      val buff = combine(v1, v2)
      // println(buff.map{case(states,unifs) =>
      //   states.mkString(" || ")+"; "+unifs}.mkString("\n"))
      // Just identity mapping since N0 fixed
      assert(buff.length == 1 && buff.forall{case(Array(st1, st2), unifs) =>
        st1 == aNode(0,1) && st2 == aNode(1,2) && unifs == List((1,0)) })
    }
    test1; test2; test3; test4; test5; test6
  }

  def remapSelectedStatesTest = {
    def test1 = {
      val buff = remapSelectedStates(
        newRemappingMap, Array(List(1), List(0)), Array(2,1),
        Array(aNode(0,1)), Left(0))
      // N1 -> N1 or N2
      assert(buff.length == 2)
      assert(buff.forall(map => 
        (checkMap(map(0), List((1,1))) || checkMap(map(0), List((1,2)))) && 
          emptyMap(map(1)) ))
    }
    def test2 = {
      val buff = remapSelectedStates(
        newRemappingMap, Array(List(0), List(0)), Array(1,1),
        Array(pushSt(T0,N0), aNode(0,1)), Left(0))
      // N0 -> N0 or N1
      assert(buff.length == 2)
      assert(buff.forall(map => 
        (checkMap(map(0), List((0,0))) || checkMap(map(0), List((0,1)))) && 
          emptyMap(map(1)) ))
    }   
    def test3 = {
      val map = newRemappingMap; map(0)(0) = 0
      val buff = remapSelectedStates(map, Array(List(1), List(0)), Array(2,1),
        Array(pushSt(T0,N0), aNode(0,1)), Left(0))
      // Must respect map
      assert(buff.length == 1 && buff.head == map)
    }

    // Now tests with selector Right(i)
    def test11 = {
      val buff = remapSelectedStates(
        newRemappingMap, Array(List(1), List(0)), Array(2,1),
        Array(aNode(0,1)), Right(0)) 
      assert(buff.length == 1 && buff.head.forall(m => emptyMap(m)))
    }
    def test12 = {
      val map = newRemappingMap; map(0)(0) = 0
      val buff = remapSelectedStates(map, Array(List(1), List(0)), Array(2,1),
        Array(pushSt(T0,N0), aNode(0,1)), Right(0))
      // N0 -> N0 and N1 -> N1 or N2
      assert(buff.length == 2)
      assert(buff.forall(map => 
        (checkMap(map(0), List((0,0), (1,1))) || checkMap(map(0), List((0,0), (1,2)))
        ) && emptyMap(map(1)) ))
    }    
    def test13 = {
      val map = newRemappingMap; map(0)(0) = 0
      val buff = remapSelectedStates(map, Array(List(1), List(1)), Array(2,2),
        Array(pushSt(T0,N0), aNode(0,1)), Right(1))
      // println(buff.map(showRemappingMap).mkString("\n"))
      // N0 -> N1 or N2; T0 -> T1 or T2
      assert(buff.length == 2)
      assert(buff.forall(map =>
        checkMap(map(0), List((0,0))) &&
          (checkMap(map(1), List((0,1))) || checkMap(map(1), List((0,2))))
      ))
    }

    test1; test2; test3; test11; test12; test13
  }

  private def remapToIdTest = {
    def test1 = {
      val buff = remapToId(newRemappingMap, Array(List(N2), List(T0)), Array(N3,T1),
        Array(aNode(N0,N1)), 0, N1)
      // Maps N0 -> N1 and N1 -> N2 or N3
      assert(buff.length == 2)
      assert(buff.forall(map =>
        (checkMap(map(0), List((N0,N1), (N1,N2))) || 
          checkMap(map(0), List((N0,N1), (N1,N3)))
        ) && emptyMap(map(1))))
    }
    def test2 = {
      val map = newRemappingMap; map(0)(N1) = N2
      val buff = remapToId(map, Array(List(N0,N3), List(T0)), Array(N4,T1),
        Array(pushSt(T0,N0), aNode(N0,N1)), 1, N1)
      // N0 -> N1 and N1 -> N2, as in map
      assert(buff.length == 1 && checkMap(buff.head(0), List((N0,N1), (N1,N2))) &&
        emptyMap(buff.head(1)))
    }
    def test3 = {
      val map = newRemappingMap; map(1)(T0) = T1
      val buff = remapToId(map, Array(List(N0,N3), List(T0)), Array(N4,T2),
        Array(pushSt(T0,N0), aNode(N0,N1)), 0, T1)
      // println(buff.map(showRemappingMap).mkString("\n"))
      // T0 -> T1 and N0 -> N0, N3 or N4
      assert(buff.length == 3)
      assert(buff.forall(map =>
        (checkMap(map(0), N0, N0) || checkMap(map(0), N0, N3) || 
          checkMap(map(0), N0, N4)) &&
          checkMap(map(1), T0, T1)))
    }

    test1; test2; test3
  }

  /** Test for remapRest. */
  private def remapRestTest = {
    def test1 = {
      val map = newRemappingMap; map(0)(N0) = N0; map(0)(N1) = N2
      val buff = remapRest(map, Array(List(N3), List(T0)), 
        Array(aNode(N0,N1)), 0)
      // Just remaps the single state as per map
      assert(buff.forall(sts => sts.length == 1 && sts(0) == aNode(N0,N2)))
    }
    def test2 = {
      val map = newRemappingMap; map(0)(N0) = N1; map(1)(T0) = T1
      val buff = remapRest(map, Array(List(N0,N2), List(T0)), 
        Array(pushSt(T0,N0), aNode(N0,N1)), 0)
      // pushSt(T1,N1) || aNode(N1, N0|N2|N3)
      assert(buff.length == 3 && buff.forall(sts =>
        sts.length == 2 && sts(0) == pushSt(T1,N1) &&
          (sts(1) == aNode(N1,N0) || sts(1) == aNode(N1,N2) || sts(1) == aNode(N1,N3))
      ))
    }
    def test3 = {
      val map = newRemappingMap; map(0)(N0) = N1; map(0)(N1) = N2
      val buff = remapRest(map, Array(List(N0), List(T0)), 
        Array(pushSt(T0,N0), aNode(N0,N1)), 1)
      //println(buff.map(showStates).mkString("\n"))
      // pushSt(T0|T1, N1) || aNode(N1,N2)
      assert(buff.length == 2 && buff.forall(sts =>
        sts.length == 2 && (sts(0) == pushSt(T0,N1) || sts(0) == pushSt(T1,N1)) &&
          sts(1) == aNode(N1,N2)
      ))
    }

    test1; test2; test3
  }

  def test = {
    createCombiningMapsTest
    createMaps1Test
    unifyTest
    combine1Test
    combineTest
    remapSelectedStatesTest
    remapToIdTest
    remapRestTest
  }

}
