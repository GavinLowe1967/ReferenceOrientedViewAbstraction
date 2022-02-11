package ViewAbstraction

import RemapperP._
import scala.collection.mutable.ArrayBuffer

object RemappingExtenderTest{

  import TestStates._
  import TestUtils._
  import Unification.UnificationList // = List[(Int,Int)]

  private def showCandMap(candMap: Array[Array[List[Identity]]]): String = 
    candMap.map(_.mkString(", ")).mkString("; ")

  private def mkOABitMap(size: Int, values: List[Int]) = {
    assert(values.forall(i => i >= 0 && i < size))
    Array.tabulate(size)(i => values.contains(i))
  }

  /** Test based on (servers(N0); Th(T0,N1), Nd_A(N1,N2)) -> 
    *     (servers(N1); Th'(T0,N1), Nd_A(N1,N2)
    * acting on (servers(N0), Nd_B(N1,N2), Nd_C(N2,Null)).  */
  private def test1 = {
    println("=test1=")
    val pre = new Concretization(servers3(N0), 
      Array(initNodeSt(T0,N1), aNode(N1,N2)))
    val post = new Concretization(servers3(N1), 
      Array(pushSt(T0,N1), aNode(N1,N2)))
    val cv = new ComponentView(servers3(N0), Array(bNode(N1,N2), cNode(N2,Null)))
    val remappingExtender = new RemappingExtender(pre, post, cv)
    val testHooks = remappingExtender.TestHooks
    val unifs: UnificationList = List()
    val oaBitMap = Array(mkOABitMap(3,List(N1)), mkOABitMap(1,List()))
    val rdMap: RemappingMap = Array(Array(N0,-1,-1), Array())

    assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
    assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

    // Following doesn't apply to actual linkage
    val candMap = testHooks.getCandidatesMap(oaBitMap, rdMap, List())
    // Can map N1 -> N2, N2 -> N2 (but not both) 
    assert(candMap(0)(N0).isEmpty && candMap(0)(N1) == List(N2) &&
      candMap(0)(N2) == List(N2) && candMap(1).isEmpty)
    val extMaps = testHooks.extendMapToCandidates(rdMap, candMap)
    assert(extMaps.length == 3)
    for(em <- extMaps)
      assert(em(0)(N0) == N0 && List(2,-1).contains(em(0)(N1)) && 
        List(2,-1).contains(em(0)(N2)) && Remapper.isInjective(em) && 
        em(1).isEmpty)

    val eMaps = remappingExtender.makeExtensions(unifs,oaBitMap,rdMap,true)
    assert(eMaps.length == 1); val eMap = eMaps(0)
    // Must map N1,N2 to fresh values
    assert(checkMap(eMap(0), List((N0,N0),(N1,N3),(N2,N4))) &&
      emptyMap(eMap(1)))
  }

  /* Test based on (fixed(N0); Th(T0, N1, N2), Nd_A(N1, N3)) ->
   *  (fixed(N4); Th'(T0, N1, N2), Nd_C(N1, N2)),
   * acting on (fixed(N0); Nd_A(N1, N2), Nd_B(N2, N3)).
   */
  private def test2 = {
    println("=test2=")
    val pre = new Concretization(servers3(N0), 
      Array(getDatumSt(T0, N1, N2), aNode(N1, N3)))
    val post = new Concretization(servers3(N4),
      Array(getDatumSt(T0, N1, N2), cNode(N1, N2)))
    val cv = new ComponentView(servers3(N0), Array(aNode(N1, N2), bNode(N2, N3)))
    val remappingExtender = new RemappingExtender(pre, post, cv)
    val testHooks = remappingExtender.TestHooks

    { // No unification
      val unifs: UnificationList = List()
      val oaBitMap = Array(mkOABitMap(5,List(N4)), mkOABitMap(0,List()))
      // N0 -> N0, N1/N2/N3/- -> N4
      for(n <- List(-1,N1,N2,N3)){
        val rdMap: RemappingMap = Array(Array(N0,-1,-1,-1), Array())
        if(n >= 0) rdMap(0)(n) = N4
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        val eMaps = remappingExtender.makeExtensions(unifs,oaBitMap,rdMap,true)
        assert(eMaps.length == 1); val eMap = eMaps(0); assert(emptyMap(eMap(1)))
        // Map other values to fresh
        if(n == N1)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N4), (N2,N5), (N3,N6))))
        else if(n == N2)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N4), (N3,N6))))
        else if(n == N3)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N4))))
        else
          assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N7))))
      }

      // Secondary induced transitions by mapping N1 -> N2
      val oaBitMap1 = Array(mkOABitMap(5,List(N1,N4)), mkOABitMap(1,List()))
      val otherArgs1 = Array(List(N1,N4), List())
      val srdMap: RemappingMap = Array(Array(N0,N2,-1,-1), Array())
      val rdsMaps = remappingExtender.extendMapOverComponent(
        srdMap, cv.components(0), otherArgs1)
      // Can map N2 -> N4/-; can't map to N1 as that would imply a unification
      assert(rdsMaps.length == 2)
      for(rdMap <- rdsMaps){
        val n = rdMap(0)(N2)
        assert(emptyMap(rdMap(1)) && (n == N4 || n < 0) &&
          checkMap(rdMap(0), List((N0,N0), (N1,N2), (N2,n))))
        assert(testHooks.findLinkages(unifs, rdMap) == List( (0,0) ))
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        // Following is hypothetical as there are no common missing components
        val candMap = testHooks.getCandidatesMap(oaBitMap1, rdMap, List((0,0)))
        // Can map undefined params to N3, only
        assert(candMap(0)(N0).isEmpty && candMap(0)(N1).isEmpty && 
          candMap(0)(N3) == List(N3) && candMap(1).isEmpty)
        if(n == N4) assert(candMap(0)(N2).isEmpty) 
        else assert(candMap(0)(N2) == List(N3))
        val extMaps = testHooks.extendMapToCandidates(rdMap, candMap)
        if(n == N4) assert(extMaps.length == 2) else assert(extMaps.length == 3)
        for(em <- extMaps){
          assert(Remapper.isInjective(em) && em(0)(N0) == N0 && em(0)(N1) == N2 && 
            List(N3,-1).contains(em(0)(N3)) && em(1).isEmpty)
          if(n == N4) assert(em(0)(N2) == N4) 
          else assert(List(N3,-1).contains(em(0)(N2)))
        }

        val candMap1 = testHooks.getCandidatesMap(oaBitMap1, rdMap, List((0,1)))
        // Now can't map N2 to N3; can map N3 -> N3
        assert(List(N0,N1,N2).forall(n => candMap1(0)(n).isEmpty) &&
          candMap1(0)(N3) == List(N3) && candMap1(1).isEmpty)
        val extMaps1 = testHooks.extendMapToCandidates(rdMap, candMap1)
        assert(extMaps1.length == 2)
        for(em <- extMaps1)
          assert(List(N0,N1,N2).forall(n => em(0)(n) == rdMap(0)(n)) &&
            List(N3,-1).contains(em(0)(N3)) && em(1).isEmpty)

        val eMaps = remappingExtender.makeExtensions(unifs,oaBitMap1,rdMap,true)
        // Other values map to fresh; again can't map N2 -> N1
        assert(eMaps.length == 1); val eMap = eMaps(0); assert(eMap(1).isEmpty)
        if(n == N4) assert(eMap(0).sameElements(Array(N0,N2,N4,N5)))
        else assert(eMap(0).sameElements(Array(N0,N2,N5,N6)))
      }
    }

    { // With unification of Nd_A,s
      val unifs1: UnificationList = List((0,1))
      val oaBitMap = Array(mkOABitMap(5,List(N2,N4)), mkOABitMap(1,List()))
      val map1List = List((N0,N0), (N1,N1), (N2,N3))
      // N0 -> N0, N1 -> N1, N2 -> N3, N3 -> N2, N4 or -1
      for(n <- List(N2,N4,-1)){
        val rdMap: RemappingMap = Array(Array(N0,N1,N3,n), Array())
        assert(testHooks.findLinkages(unifs1, rdMap).isEmpty)
        assert(testHooks.findLinkagesC(unifs1, rdMap).isEmpty)

        // Following is hypothetical
        val candMap = testHooks.getCandidatesMap(oaBitMap, rdMap, List())
        // All params are result-defining or in range rdMap
        assert(candMap(0).forall(_.isEmpty) && candMap(1).isEmpty)
        val extMaps = testHooks.extendMapToCandidates(rdMap, candMap)
        assert(extMaps.length == 1); val em = extMaps(0)
        assert(checkMap(em(0), List((N0,N0), (N1,N1), (N2,N3), (N3,n))) && 
          emptyMap(em(1)))

        val eMaps = remappingExtender.makeExtensions(unifs1,oaBitMap,rdMap,true)
        assert(eMaps.length == 1); val eMap = eMaps(0)
        val map1List = List((N0,N0), (N1,N1), (N2,N3), (N3,if(n >= 0) n else N5))
        assert(checkMap(eMap(0), map1List) && emptyMap(eMap(1)))
      }
    }
  }


  /* Test based on (fixed(N0); Th(T0, N1, N2), Nd_A(N1, N3), Nd_B(N_2,N_4)) ->
   *  (fixed(N5); Th'(T0, N1, N2), Nd_C(N1, N2), Nd_B(N_2,N_4)),
   * acting on (fixed(N0); Nd_A(N1, N2), Nd_B(N2, N3)).
   */
  def test3 = {
    println("=test3=")
    val pre = new Concretization(servers3(N0), 
      Array(getDatumSt(T0, N1, N2), aNode(N1, N3), bNode(N2,N4)))
    val post = new Concretization(servers3(N5),
      Array(getDatumSt(T0, N1, N2), cNode(N1, N2), bNode(N2,N4)))
    val cv = new ComponentView(servers3(N0), Array(aNode(N1, N2), bNode(N2, N3)))
    val remappingExtender = new RemappingExtender(pre, post, cv)
    val testHooks = remappingExtender.TestHooks

    {    // No unification
      val unifs: UnificationList = List()
      val oaBitMap = Array(mkOABitMap(6,List(N5)), mkOABitMap(1,List()))

      // N0 -> N0 and N1/N2/N3/nothing -> N5
      val rdMap: RemappingMap = Array(Array(N0,-1,-1,-1), Array())
      assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
      assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
      for(n <- List(N1,N2,N3)){
        val rdMap: RemappingMap = Array(Array(N0,-1,-1,-1), Array())
        rdMap(0)(n) = N5
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        // Following is hypothetical
        val candMap = testHooks.getCandidatesMap(oaBitMap, rdMap, List())
        assert(candMap(0)(N0).isEmpty && candMap(0)(n).isEmpty && 
          candMap(1).isEmpty)
        // N1 and N2 can't be mapped to another id (N1 or N2); so just N3/N4
        for(n1 <- List(N1,N2); if n1 != n)
          assert(candMap(0)(n1).sorted == List(N3,N4))
        // N3 can map to anything except N0,N5
        if(N3 != n) assert(candMap(0)(N3).sorted == List(N1,N2,N3,N4))
        val extMaps = testHooks.extendMapToCandidates(rdMap, candMap)
        if(n == N3) assert(extMaps.length == 7) // = 2(N1->N3)+2(N1->N4)+3(N1->_)
        else assert(extMaps.length == 13) // 4+4+5
        for(em <- extMaps)
          assert(Remapper.isInjective(em) && em(0)(N0) == N0 && em(0)(n) == N5 &&
            (n == N2 || List(N3,N4,-1).contains(em(0)(N2))) && 
            List(N1,N3).forall(n1 => 
              n1 == n || List(N1,N2,N3,N4,-1).contains(em(0)(n1))) &&
            em(1).isEmpty)

        // With link (0,2)
        val candMap1 = testHooks.getCandidatesMap(oaBitMap, rdMap, List((0,2)))
        assert(candMap1(0)(N0).isEmpty && candMap1(0)(n).isEmpty && 
          candMap1(1).isEmpty)
        // Can't map N1/N2 to N1(id)/N2/N4; can map N1/N2 (except n) -> N3;
        // and N3 (if not n) -> N1/N2/N3/N4
        for(n1 <- List(N1,N2); if n1 != n) assert(candMap1(0)(n1) == List(N3))
        if(n != N3) assert(candMap1(0)(N3).sorted == List(N1,N2,N3,N4))
        val extMaps1 = testHooks.extendMapToCandidates(rdMap, candMap1)
        if(n != N3) assert(extMaps1.length == 9) // 4(N2->N3)+5(N2->-)
        else assert(extMaps1.length == 3) 
        for(em <- extMaps1)
          assert(Remapper.isInjective(em) && em(0)(N0) == N0 && em(0)(n) == N5 &&
            List(N1,N2).forall(n1 => 
              n1 == n || List(N3,-1).contains(em(0)(n1))) &&
            (n == N3 || List(N1,N2,N3,N4,-1).contains(em(0)(N3))) )

        val eMaps = remappingExtender.makeExtensions(unifs,oaBitMap,rdMap,true)
        assert(eMaps.length == 1); val eMap = eMaps(0)
        // Maps all other params to fresh params
        assert(emptyMap(eMap(1)))
        if(n == N1)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N7))))
        else if(n == N2)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N6), (N2,N5), (N3,N7))))
        else if(n == N3)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N6), (N2,N7), (N3,N5))))
        else
          assert(checkMap(eMap(0), List((N0,N0), (N1,N6), (N2,N7), (N3,N8))))
      }
    }

    { // Unify the Nd_A's
      val unifs: UnificationList = List((0,1))
      val oaBitMap = Array(mkOABitMap(6,List(N2,N4,N5)), mkOABitMap(1,List()))
      // N0 -> N0, N1 -> N1, N2 -> N3, N3 -> N2/N4/N5/-1
      for(n <- List(N2,N4,N5,-1)){
        val rdMap: RemappingMap = Array(Array(N0,N1,N3,n), Array())
        val linkages = testHooks.findLinkages(unifs, rdMap).toList
        if(rdMap(0)(N3) == N2){  // linkage Nd_B -> Nd_B via N3 -> N2
          assert(linkages.sorted == List((1,2)))
          // Following is hypothetical.
          val candMap = testHooks.getCandidatesMap(oaBitMap, rdMap, linkages)
          // rdMap is total, so all empty
          assert(candMap(0).forall(_.isEmpty) && candMap(1).isEmpty)
          val extMaps = testHooks.extendMapToCandidates(rdMap, candMap)
          assert(extMaps.length == 1); val em = extMaps(0)
          assert(em(0).sameElements(rdMap(0)) && em(1).isEmpty)
        }
        else assert(linkages.isEmpty)

        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        val map1List = List((N0,N0), (N1,N1), (N2,N3), (N3,if(n >= 0) n else N6))
        val eMaps = remappingExtender.makeExtensions(unifs,oaBitMap,rdMap,true)
        assert(eMaps.length == 1); val eMap = eMaps(0)
        assert(checkMap(eMap(0), map1List) && emptyMap(eMap(1)))
      }
    }

    { // unify the Nd_B's
      val unifs = List((1,2))
      val oaBitMap = Array(mkOABitMap(6,List(N5)), mkOABitMap(0,List()))
      // N0 -> N0, N1 -> N5/-, N2 -> N2, N3 -> N4
      for(n <- List(N5,-1)){
        val rdMap: RemappingMap = Array(Array(N0,n,N2,N4), Array())
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        val map1List = List((N0,N0), (N1,if(n >= 0) n else N6), (N2,N2), (N3,N4))
        val eMaps = remappingExtender.makeExtensions(unifs,oaBitMap,rdMap,true)
        assert(eMaps.length == 1); val eMap = eMaps(0)
        assert(checkMap(eMap(0), map1List) && emptyMap(eMap(1)))
      }
    }
  }


  /* Test based on (fixed(N0); Th(T0, N1, N2), Nd_A(N1, N3)) ->
   *   (fixed(N4); Th'(T0, N1, N2), Nd_B(N1,N2))
   * acting on (fixed(N0); Th(T0, N1, N2), Nd_A(N1, N3)). */
  def test4 = {
    println("=test4=")
    val pre = new Concretization(servers3(N0), 
      Array(getDatumSt(T0, N1, N2), aNode(N1, N3)))
    val post = new Concretization(servers3(N4),
      Array(getDatumSt(T0, N1, N2), bNode(N1, N2)))
    val cv = new ComponentView(servers3(N0), 
      Array(getDatumSt(T0, N1, N2), aNode(N1, N3)))
    val remappingExtender = new RemappingExtender(pre, post, cv)
    val testHooks = remappingExtender.TestHooks

    {                                                  // No unifications
      val unifs: UnificationList = List()
      val oaBitMap = Array(mkOABitMap(5,List(N4)), mkOABitMap(1,List()))
      // N0 -> N0, N1/N2/N3/- -> N4
      val rdMap : RemappingMap = Array(Array(N0,-1,-1,-1), Array(-1))
      assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
      assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
      for(n <- List(N1,N2,N3)){
        val rdMap : RemappingMap = Array(Array(N0,-1,-1,-1), Array(-1))
        rdMap(0)(n) = N4
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        val eMaps = remappingExtender.makeExtensions(unifs,oaBitMap,rdMap,true)
        assert(eMaps.length == 1); val eMap = eMaps(0)
        // Maps all other params to fresh params
        assert(checkMap(eMap(1), List((T0,T1))))
        if(n == N1)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N4), (N2,N5), (N3,N6))))
        else if(n == N2)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N4), (N3,N6))))
        else if(n == N3)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N4))))
        else
          assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N7))))
      }
    }

    {                                                  // Unify the Nd_A's
      val unifs: UnificationList = List((1,1))
      val oaBitMap = Array(mkOABitMap(5,List(N2,N4)), mkOABitMap(1,List()))
      // N0 -> N0, N1 -> N1, N2 -> N2/N4/-, N3 -> N3
      for(n <- List(N2,N4,-1)){
        val rdMap : RemappingMap = Array(Array(N0,N1,n,N3), Array(-1))
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        val linkagesC = testHooks.findLinkagesC(unifs, rdMap)
        if(n == N2)  // Common missing component with id N2
          assert(linkagesC == List((0,N2)))
        else assert(linkagesC.isEmpty)

        val candMap = testHooks.getCandidatesMap(oaBitMap, rdMap, List())
        // rdMap defined over all Node IDs; cannot map T0 -> T0
        assert(candMap(0).forall(_.isEmpty) && candMap(1)(T0) == List())
        val extMaps = testHooks.extendMapToCandidates(rdMap, candMap)
        assert(extMaps.length == 1); val em = extMaps(0)
        assert(em(0).sameElements(rdMap(0)) && em(1)(T0) == -1)

        val eMaps = remappingExtender.makeExtensions(unifs,oaBitMap,rdMap,true)
        assert(eMaps.length == 1); val eMap = eMaps(0)
        assert(checkMap(eMap(1), List((T0,T1)))) // can't map T0 -> T0
        val map1List = List((N0,N0), (N1,N1), (N2, if(n < 0) N5 else n), (N3,N3))
        assert(checkMap(eMap(0), map1List))
      }
    }
  }

  /** Test based on (fixed(N0); Th(T0, N1), Nd_A(N1,N0)) ->
    *   (fixed(N2); Th'(T0), Nd_A(N1,N0))
    * acting on  (fixed(N0); Th''(T0, N0), Nd_B(N0,N1)). */
  def test5 = {
    println("=test5=")
    val pre = new Concretization(servers3(N0), 
      Array(pushSt(T0, N1), aNode(N1, N0)))
    val post = new Concretization(servers3(N2), Array(unlock(T0), aNode(N1, N0)))
    val cv = new ComponentView(servers3(N0), 
      Array(setTopB(T0, N0), bNode(N0, N1)))
    val remappingExtender = new RemappingExtender(pre, post, cv)
    val testHooks = remappingExtender.TestHooks

    val unifs: UnificationList = List()
    val oaBitMap = Array(mkOABitMap(4,List(N2)), mkOABitMap(1,List()))
    // N0 -> N0, N1 -> N2/-1
    for(n <- List(N2,-1)){
      val rdMap : RemappingMap = Array(Array(N0,n), Array(-1))
      assert(testHooks.findLinkages(unifs, rdMap) == List((1,1)))
      assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
      // Following is hypothetical
      val candMap = testHooks.getCandidatesMap(oaBitMap, rdMap, List((1,1)))
      // Can't map N1 -> N1 because of linkage; cannot map T0 -> T0
      assert(candMap(0).forall(_.isEmpty) && candMap(1)(T0) == List())
      val extMaps = testHooks.extendMapToCandidates(rdMap, candMap)
      assert(extMaps.length == 1); val em = extMaps(0)
      assert(em(0).sameElements(rdMap(0)) && rdMap(1)(T0) == -1)

      val eMaps = remappingExtender.makeExtensions(unifs,oaBitMap,rdMap,true)
      if(n == N2){
        assert(eMaps.length == 1); val eMap = eMaps(0)
        // Map T0 to fresh value
        assert(checkMap(eMap(0), List((N0,N0), (N1,N2))) &&
          checkMap(eMap(1), List((T0,T1))))
      }
      else{
        assert(eMaps.length == 2 && eMaps.forall(eMap => 
          checkMap(eMap(1), List((T0,T1))) &&
            List(N1,N3).exists(n1 => checkMap(eMap(0), List((N0,N0),(N1,n1))))))
      }
    }
  }

  /** Main function. */
  def apply() = {
    singleRef = true
    println("===RemappingExtenderTest===")
    test1; test2; test3; test4; test5
  }

}
