package ViewAbstraction.CombinerP

import ViewAbstraction._
import scala.collection.mutable.ArrayBuffer

/** Testing functions on Combiner.  These assume that test-file.csp is
  * loaded. */
object CombinerTest{
  import RemapperP.Remapper.{newRemappingMap,newOtherArgMap,show}
  import RemapperP.RemapperTest.{checkMap,emptyMap}
  import CombinerP.Combiner._
  import TestStates._

  /** Test of remapSelectedStates. */
  def remapSelectedStatesTest = {
    println("== remapSelectedStatesTest ==")
    def test1 = {
      val buff = remapState(
        newRemappingMap, Array(List(1), List(0)), Array(2,1), aNode(0,1), 0)
        // Array(aNode(0,1)), Left(0))
      // println(buff.map(show).mkString("\n"))
      // N0 -> N1, N1 -> N2 or N0 -> N2, N1 -> N1 or N0 -> N2, N1 -> N3
      assert(buff.length == 3)
      assert(buff.forall(map =>
        (checkMap(map(0), List((0,1), (1,2))) || checkMap(map(0), List((0,2),(1,1))) ||
          checkMap(map(0), List((0,2), (1,3)))) &&
          emptyMap(map(1)) ))
    }
    def test2 = {
      val buff = remapState(
        newRemappingMap, Array(List(0), List(0)), Array(1,1), pushSt(T0,N0), 0)
        // Array(pushSt(T0,N0), aNode(0,1)), Left(0))
      // N0 -> N0 or N1; T0 -> T0 or T1
      //println(buff.map(show).mkString("\n"))
      assert(buff.length == 4)
      assert(buff.forall(map => 
        (checkMap(map(0), List((0,0))) || checkMap(map(0), List((0,1)))) && 
          (checkMap(map(1), List((0,0))) || checkMap(map(1), List((0,1)))) ))
    }   
    def test3 = {
      val map = newRemappingMap; map(0)(0) = 0
      val buff = remapState(map, Array(List(1), List(0)), Array(2,1), pushSt(T0,N0), 0)
        //Array(pushSt(T0,N0), aNode(0,1)), Left(0))
      // println(buff.map(show).mkString("\n"))
      // Must respect map on N0; T0 -> T0 or T1
      assert(buff.length == 2)
      assert(buff.forall(map => checkMap(map(0), List((0,0))) &&
        (checkMap(map(1), List((0,0))) || checkMap(map(1), List((0,1)))) ))
    }

    // Now tests with selector Right(i)
    def test11 = {
      val buff = remapSelectedStates(
        newRemappingMap, Array(List(1), List(0)), Array(2,1),
        Array(aNode(0,1)), 0) 
      assert(buff.length == 1 && buff.head.forall(m => emptyMap(m)))
    }
    def test12 = {
      val map = newRemappingMap; map(0)(0) = 0
      val buff = remapSelectedStates(map, Array(List(1), List(0)), Array(2,1),
        Array(pushSt(T0,N0), aNode(0,1)), 0)
      // N0 -> N0 and N1 -> N1 or N2
      assert(buff.length == 2)
      assert(buff.forall(map => 
        (checkMap(map(0), List((0,0), (1,1))) || 
          checkMap(map(0), List((0,0), (1,2)))
        ) && emptyMap(map(1)) ))
    }    
    def test13 = {
      val map = newRemappingMap; map(0)(0) = 0
      val buff = remapSelectedStates(map, Array(List(1), List(1)), Array(2,2),
        Array(pushSt(T0,N0), aNode(0,1)), 1)
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

  // /** Test of remapToId. */
  private def remapToIdTest = {
    println("== remapToIdTest ==")
    def test1 = {
      val buff = remapToId(newRemappingMap, Array(List(N2), List(T0)), Array(N3,T1),
        aNode(N0,N1), N1)
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
        aNode(N0,N1), N1)
      // N0 -> N1 and N1 -> N2, as in map
      assert(buff.length == 1 && checkMap(buff.head(0), List((N0,N1), (N1,N2))) &&
        emptyMap(buff.head(1)))
    }
    def test3 = { 
      val map = newRemappingMap; map(1)(T0) = T1
      val buff = remapToId(map, Array(List(N0,N3), List(T0)), Array(N4,T2),
        pushSt(T0,N0), T1)
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
    // Note: test1 now fails precondition of remapRest
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
          (sts(1) == aNode(N1,N0) || sts(1) == aNode(N1,N2) || 
            sts(1) == aNode(N1,N3))
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

    // test1; // no longer valid
    test2; test3
  }

  /** Test for areUnifiable. */
  def areUnifiableTest = {
    println("== areUnifiableTest ==")
    def test1 = {
      val map = newRemappingMap; val otherArgs = newOtherArgMap
      // Following is trivial
      assert(areUnifiable(Array(aNode(N0,Null)), Array(aNode(N1, Null)), 
        map, 0, otherArgs))
      val cpts1 = Array(pushSt(T0, N0), aNode(N0,Null))
      map(0)(N0) = N0; map(1)(T0) = T0
      // aNode(N0,Null) => aNode(N0,Null) so no common components
      assert(areUnifiable(cpts1, Array(aNode(N1, Null)), map, 0, otherArgs))
      // aNode(N0,Null) => aNode(N0,Null) so matches
      assert(areUnifiable(cpts1, Array(aNode(N0, Null)), map, 0, otherArgs))
      // But doesn't match following
      assert(!areUnifiable(cpts1, Array(aNode(N0, N1)), map, 0, otherArgs))
      assert(!areUnifiable(cpts1, Array(bNode(N0, Null)), map, 0, otherArgs))
    }

    def test2 = {
      val map = newRemappingMap; val otherArgs = newOtherArgMap
      val cpts1 = Array(pushSt(T0, N0), aNode(N0,N1))
      map(0)(N0) = N0; map(1)(T0) = T0
      otherArgs(0) = List(N1)
      //  aNode(N0,N1) => aNode(N0,N1) 
      assert(areUnifiable(cpts1, Array(aNode(N0, N1)), map, 0, otherArgs))
      // aNode(N0,N1) => aNode(N0,N2)
      assert(areUnifiable(cpts1, Array(aNode(N0, N2)), map, 0, otherArgs))

      otherArgs(0) = List(N1,N2)
      //  aNode(N0,N1) => aNode(N0,N1) 
      assert(areUnifiable(cpts1, Array(aNode(N0, N1)), map, 0, otherArgs))
      //  N1 => N1
      assert(areUnifiable(cpts1, Array(aNode(N0, N1)), map, 0, otherArgs))
      // aNode(N0,N1) => aNode(N0,N2)
      assert(areUnifiable(cpts1, Array(aNode(N0, N2)), map, 0, otherArgs))

      otherArgs(0) = List(N2)
      // Now can't have aNode(N0,N1) => aNode(N0,N1)
      assert(! areUnifiable(cpts1, Array(aNode(N0, N1)), map, 0, otherArgs))
      // aNode(N0,N1) => aNode(N0,N2)
      assert(areUnifiable(cpts1, Array(aNode(N0, N2)), map, 0, otherArgs))
    }

    test1; test2
  }


  /** Main test. */
  def test = {
    println("=== CombinerTest ===")
    remapSelectedStatesTest
    remapToIdTest
    remapRestTest
    areUnifiableTest
  }
}
