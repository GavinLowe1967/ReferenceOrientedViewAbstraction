package ViewAbstraction.RemapperP 

import ViewAbstraction._
import scala.collection.mutable.ArrayBuffer

/** Testing functions on Remapper.  These assume that test-file.csp is
  * loaded. */
object RemapperTest{
  import RemapperP.Remapper._
  import RemapperP.Unification._
  import TestStates._

  // ======== Helper functions

  /** Check that map is the mapping {i -> j}. */
  def checkMap(map: Array[Int], i: Int, j: Int) =
    map(i) == j && map.indices.forall(i1 => i1 == i || map(i1) == -1)

  /** Check that map is the mapping {(i,j) | (i,j) <- pairs}. */
  def checkMap(map: Array[Int], pairs: List[(Int,Int)]) =
    map.indices.forall(i => pairs.filter(_._1 == i) match{
      case List() => map(i) == -1
      case List((i1,j)) => map(i) == j
    })

  def emptyMap(map: Array[Int]) = map.forall(_ == -1)

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
 
/*
  private def combine1Test = {
    println("== combine1Test ==")
    def showBuff(buff: ArrayBuffer[(Array[State], Int)]) = 
      buff.map{case(states,unifs) => View.showStates(states)+"; "+unifs }.
        mkString("\n")
    def test1 = { // 6[0](N0), 6[0](N1), allowing N1 -> N0
      val buff = combine1(newRemappingMap, Array(1,0), Array(List(0), List()),
        Array(initNode(N0)), Array(initNode(N1)))
      assert(buff.length == 2)
      // println("test1\n"+showBuff(buff))
      assert(buff.exists{case(sts,unifs) => // mapping N1 -> N0 with unification
        sts.sameElements(Array(initNode(N0))) && unifs == 0 })
      assert(buff.exists{case(sts,unifs) => // mapping N1 -> N1
        sts.sameElements(Array(initNode(N1))) && unifs == -1 })
    }
    def test2 = { // Thread(T0) and InitNode(N0/N1)
      val buff = combine1(newRemappingMap, Array(1,1), Array(List(0), List()),
        Array(initSt(T0), initNode(N0)), Array(initSt(T0), initNode(N1)))
      assert(buff.length == 2)
      // println("test2\n"+showBuff(buff))
      assert(buff.exists{case(sts,unifs) => // N1 -> N0, with unification, T0 -> T1
        sts.sameElements(Array(initSt(T1), initNode(N0))) && unifs == -1 })
      assert(buff.exists{case(sts,unifs) => // N1 -> N1, no unification, T0 -> T1
        sts.sameElements(Array(initSt(T1), initNode(N1))) && unifs == -1 })
    }
    def test3 = { // Thread(T0) and InitNode(N0/N1)
      val buff = combine1(newRemappingMap, Array(1,1), Array(List(0), List(0)),
        Array(initSt(T0), initNode(N0)), Array(initSt(T0), initNode(N1)))
      assert(buff.length == 4)
      // println("test3\n"+showBuff(buff))
      assert(buff.forall{case(sts,unifs) =>
        // N1 -> N0 or N1 -> N1
        ( sts.contains(initNode(N0)) || sts.contains(initNode(N1)) ) &&
        // T0 -> T0 with unification; or T0 -> T1 without unification
        ( sts.contains(initSt(T0)) && unifs == 0  ||
          sts.contains(initSt(T1)) && unifs < 0 )
      })
    }
    def test4 = { // 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,N1) || 7[0](N1,N2)
      val buff = combine1(newRemappingMap, Array(2,1), Array(List(0), List(0)),
        components1, nodes)
      assert(buff.length == 4)
      // println("test4\n"+showBuff(buff))
      assert(buff.exists{case(sts,unifs) => // N0 -> N0, N1 -> N1 with unif, N2 -> N2
        sts.sameElements(Array(aNode(N0,N1), aNode(N1,N2))) && unifs == 1 })
      assert(buff.exists{case(sts,unifs) => // N1 -> N0, N2 -> N1 with unif; N0 -> N2
        sts.sameElements(Array(aNode(N2,N0), aNode(N0,N1))) && unifs < 0 })
      assert(buff.exists{case(sts,unifs) => // N0 -> N2, N1 -> N3, N2 -> N4, no unifs
        sts.sameElements(Array(aNode(N2,N3), aNode(N3,N4))) && unifs < 0 })
      assert(buff.exists{case(sts,unifs) => // N0 -> N2, N1 -> N3, N2 -> N0, no unifs
        sts.sameElements(Array(aNode(N2,N3), aNode(N3,N0))) && unifs < 0 })
    }
    def test5 = { 
      // 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,N1) || 7[0](N1,N2) with N1 -> N0
      val map = newRemappingMap; map(0)(1) = 0
      val buff = combine1(map, Array(2,1), Array(List(), List(0)), 
        components1, nodes)
      assert(buff.length == 1) // just second case from previous test
      // println("test5\n"+showBuff(buff))
      assert{val (sts,unifs) = buff.head; // N1 -> N0, N2 -> N1 with unif; N0 -> N2
        sts.sameElements(Array(aNode(N2,N0), aNode(N0,N1))) && unifs < 0 }
    }
    def test6 = {
      // println("test6")
      // 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,N1) || 7[0](N1,N2) with N1 -> N0
      val map = newRemappingMap; map(0)(1) = 0
      val buff = combine1(map, Array(3,1), Array(List(2), List(0)), 
        components1, nodes)
      // println("test6\n"+showBuff(buff))
      // println(buff.map{case(map1,unifs) => show(map1)+"; "+unifs}.mkString("\n"))
      // N0 maps to N2 or N3
      assert(buff.length == 2)
      assert(buff.forall{case(sts,unifs) =>
        (sts.sameElements(Array(aNode(N2,N0), aNode(N0,N1))) || 
          sts.sameElements(Array(aNode(N3,N0), aNode(N0,N1))))  && unifs < 0
      })
    }
    test1; test2; test3; test4; test5; test6
  } // end of combine1Test

  /** Test of combine. */
  private def combineTest = {
    println("== combineTest ==")
    def test1 = { // 6[0](N0), 6[0](N1)
      val v1 = new Concretization(servers1, Array(initNode(N0)))
      val v2 = new ComponentView(servers1, initNode(N1), Array())
      val buff = combine(v1, v2)
      assert(buff.length == 2)
      // N1 -> N0 with unif; or N1 -> N1
      assert(buff.forall{ case(Array(st), unifs) => 
        st == initNode(N0) && unifs == 0 || st == initNode(N1) && unifs < 0
      })
    }
    def test2 = { // 6[0](N0), 6[0](N0)
      val v1 = new Concretization(servers1, Array(initNode(N0)))
      val v2 = new ComponentView(servers1, initNode(N0), Array())
      val buff = combine(v1, v2)
      assert(buff.length == 2)
      // N0 -> N0 with unif; or N0 -> N1
      assert(buff.forall{ case(Array(st), unifs) => 
        st == initNode(N0) && unifs == 0 || st == initNode(N1) && unifs < 0
      })
    }
    def test3 = { // Thread with ref to A-node, and A-node
      val v1 = new Concretization(servers1, Array(pushSt(T0,N0), aNode(0,-1)))
      val v2 = new ComponentView(servers1, aNode(0,-1), Array())
      val buff = combine(v1, v2)
      assert(buff.length == 2)
      // N0 -> N0 with unif; or N0 -> N1
      assert(buff.forall{ case(Array(st), unifs) => 
        st == aNode(0,-1) && unifs == 1 || st == aNode(1,-1) && unifs < 0 })
    }
    def test4 = { // Thread with ref to A-node with non-null next, and A-node
                  // with null next: 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,Null)
      val v1 = new Concretization(servers1, Array(pushSt(T0,N0), aNode(0,1)))
      val v2 = new ComponentView(servers1, aNode(0,-1), Array())
      val buff = combine(v1, v2)
      // N0 -> N1 or N0 -> N2
      assert(buff.length == 2)
      assert(buff.forall{ case(Array(st), unifs) => 
        (st == aNode(1,-1) || st == aNode(2,-1)) && unifs < 0 })
    }
    def test5 = { // 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,N1) || 7[0](N1,N2)
      // println("test5")
      val v1 = new Concretization(servers1, Array(pushSt(T0,N0), aNode(0,1)))
      val v2 = new ComponentView(servers1, aNode(0,1), Array(aNode(1,2)))
      val buff = combine(v1, v2)
      // println(buff.map{case(states,unifs) =>
      //   states.mkString(" || ")+"; "+unifs}.mkString("\n"))
      // 7[0](N1,N2) || 7[0](N2,N0); List()
      // 7[0](N1,N2) || 7[0](N2,N3); List()
      // 7[0](N0,N1) || 7[0](N1,N2); List((1,0))
      // 7[0](N2,N1) || 7[0](N1,N0); List()
      // 7[0](N2,N1) || 7[0](N1,N3); List()
      // 7[0](N2,N0) || 7[0](N0,N1); List((1,1))
      // 7[0](N2,N3) || 7[0](N3,N1); List()
      // 7[0](N2,N3) || 7[0](N3,N0); List()
      // 7[0](N2,N3) || 7[0](N3,N4); List()
      assert(buff.length == 9)
      assert(buff.forall{ case(Array(st1, st2), unifs) =>
        st1 == aNode(0,1) && st2 == aNode(1,2) && unifs == 1 || // N0->N0
        st1 == aNode(2,0) && st2 == aNode(0,1) && unifs < 0 || // N1->N0
        st1 == aNode(1,2) && (st2 == aNode(2,3) || st2 == aNode(2,0)) && 
          unifs < 0 ||  // N0 -> N1
        st1 == aNode(2,1) && (st2 == aNode(1,3) || st2 == aNode(1,0)) && 
          unifs < 0 || // N1 -> N1
        st1 == aNode(2,3) && 
          (st2 == aNode(3,4) || st2 == aNode(3,0) || st2 == aNode(3,1)) && unifs < 0
           // distinct nodes
      })
    }
    def test6 = {// 12[1](T0,N0) || 7[0](N0,N1) and 7[0](N0,N1) || 7[0](N1,N2)
                 // with Top = N0
      // println("test6")
      val v1 = new Concretization(servers2, Array(pushSt(T0,N0), aNode(0,1)))
      val v2 = new ComponentView(servers2, aNode(0,1), Array(aNode(1,2)))
      // println(v1.toString+"\n"+v2)
      val buff = combine(v1, v2)
      // println(buff.map{case(states,unifs) =>
      //   states.mkString(" || ")+"; "+unifs}.mkString("\n"))
      // Just identity mapping since N0 fixed
      assert(buff.length == 1 && buff.forall{case(Array(st1, st2), unifs) =>
        st1 == aNode(0,1) && st2 == aNode(1,2) && unifs == 1 })
    }
    test1; test2; test3; test4; test5; test6
  }
 */

  def remapToPrincipalTest = {
    println("== remapToPrincipalTest ==")
    // Servers holding no IDs
    assert(remapToPrincipal(servers0, pushSt(T0,N0)) == pushSt(T0,N0))
    assert(remapToPrincipal(servers0, pushSt(T1,N1)) == pushSt(T0,N0))
    // Now servers holding T0
    assert(remapToPrincipal(servers1, pushSt(T0,N0)) == pushSt(T0,N0))
    assert(remapToPrincipal(servers1, pushSt(T1,N1)) == pushSt(T1,N0))
    assert(remapToPrincipal(servers1, pushSt(T2,N2)) == pushSt(T1,N0))
    // Now servers holding T0 and N0
    assert(remapToPrincipal(servers2, pushSt(T0,N0)) == pushSt(T0,N0))
    assert(remapToPrincipal(servers2, pushSt(T1,N1)) == pushSt(T1,N1))
    assert(remapToPrincipal(servers2, pushSt(T2,N2)) == pushSt(T1,N1))
  }


  /** Test of Unification.allUnifs. */
  def allUnifsTest = {
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
      println("test4")
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
  def combineTest = {
    println("== combineTest ==***")
    def showBuffer(buff: CombineResult) =
      buff.map{ case (states, us) => StateArray.show(states)+"; "+us }.
        mkString("\n")

    def test1 = {
      println("=test1=")
      val pre = new Concretization(servers0, 
        Array(initNodeSt(T0,N0), aNode(N0,N1)))
      val post = new Concretization(servers2, Array(unlock(T0), bNode(N0,N2)))
      val cv = new ComponentView(servers0, Array(aNode(N0,N1), cNode(N1,Null)))
      // val cv = new ComponentView(servers0, Array(aNode(N2,N3)))
      // servers0 contains no ids, servers2 contains T0, N0
      val buffer = combine(pre, post, cv) // , true
      println(showBuffer(buffer))
      // Unifying, N0 -> N0, N1 -> N1
      assert(buffer.exists{case (states, unifs) =>
        unifs == List((0,1)) && 
        states.sameElements(Array(aNode(N0,N1), cNode(N1,Null)))
      })
      // No unification
      assert(buffer.exists{case (states, unifs) =>
        unifs.isEmpty && states.sameElements(Array(aNode(N3,N4), cNode(N4,Null)))
      })
      assert(buffer.length == 2)

      effectOnChangedServersCache.clear
      val buffer2 = combine(pre, post, cv) // , false
      // Unifying, N0 -> N0, N1 -> N1
      println(showBuffer(buffer2))
      assert(buffer2.exists{case (states, unifs) =>
        unifs == List((0,1)) && 
        states.sameElements(Array(aNode(N0,N1), cNode(N1,Null)))
      })
      // No unification, N0 -> N3, N1 -> N4
      assert(buffer2.exists{case (states, unifs) =>
        unifs.isEmpty && states.sameElements(Array(aNode(N3,N4), cNode(N4,Null)))
      })
      assert(buffer2.length == 2)
    }

    def test2 = {
      println("\n=test2=")
      effectOnChangedServersCache.clear
      val pre = new Concretization(servers0, 
        Array(getDatumSt(T0,N0,N1), aNode(N0,N2), bNode(N1,N3)) )
      val post = 
        new Concretization(servers2, 
          Array(setTopB(T0,N0), bNode(N0,N1), bNode(N1,N3)) )
      val cv = new ComponentView(servers0, Array(aNode(N0,N1), cNode(N1,Null)))
      val buffer = combine(pre, post, cv) // , false
      // Note, N2 in pre is ignored as it doesn't unify 
      // println(showBuffer(buffer))
      assert(buffer.length == 2)
      // Unifying N2 -> N0, N3 -> N2
      assert(buffer.exists{case (states, unifs) =>
        unifs == List((0,1)) && 
        states.sameElements(Array(aNode(N0,N2), cNode(N2,Null)))
      })
      // No unification; N0 -> N4, N1 -> N5
      assert(buffer.exists{case (states, unifs) =>
        unifs.isEmpty && states.sameElements(Array(aNode(N4,N5), cNode(N5,Null)))
      })
    }

    def test3 = {
      println("=test3=")
      val pre = new Concretization(servers1, 
        Array(getDatumSt(T0,N0,N1), aNode(N0,N2), bNode(N1,N3)) )
      val post = 
        new Concretization(servers2, 
          Array(setTopB(T0,N0), bNode(N0,N1), bNode(N1,N3)) )
      val cv = new ComponentView(servers1, 
        Array(getDatumSt(T0,N0,Null), aNode(N0,N1)))
      val buffer = combine(pre, post, cv) // , false
      // servers1 contains T0, and the T0 components in pre and cv can't be 
      // unified.
      assert(buffer.isEmpty)
    }

    def test4 = {
      println("=test4=")
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
      val buffer = combine(pre, post, cv) // , false
      println("\n"+showBuffer(buffer))
      assert(buffer.forall{case (states, unifs) =>
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
      println("\n=test5**=")
      val pre = new Concretization(servers1, 
        Array(initNodeSt(T0,Null), initNode(N0)))
      val post = new Concretization(servers1, 
        Array(setTopB(T0,N0), bNode(N0,Null)))
      val cv = new ComponentView(servers1, Array(initNodeSt(T0,Null)))
      val buffer = combine(pre, post, cv) // , false
      println(showBuffer(buffer))

      // assert(false)
    }

    test1; test2; test3; test4; test5

  }

  def test = {
    println("=== RemapperTest ===")
    createCombiningMapsTest
    createMaps1Test
    unifyTest
    // combine1Test
    // combineTest
    remapToPrincipalTest
    allUnifsTest
    combineTest
  }

}
