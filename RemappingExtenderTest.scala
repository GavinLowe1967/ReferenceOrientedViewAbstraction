package ViewAbstraction


object RemappingExtenderTest{

  import TestStates._
  import TestUtils._
  import Unification.UnificationList // = List[(Int,Int)]

  private def mkOABitMap(size: Int, values: List[Int]) = 
    Array.tabulate(size)(i => values.contains(i))

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
    val rdMap: RemappingMap = Array(Array(N0,-1,-1), Array())
    assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
    assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

    val oaBitMap = Array(mkOABitMap(3,List(N1)), mkOABitMap(0,List()))
    val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap)
    assert(eMaps.length == 1); val eMap = eMaps(0)
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
      val oaBitMap = Array(mkOABitMap(4,List(N4)), mkOABitMap(0,List()))
      // N0 -> N0, one of N1,N2,N3 -> N4
      for(n <- List(N1,N2,N3)){
        val rdMap: RemappingMap = Array(Array(N0,-1,-1,-1), Array())
        rdMap(0)(n) = N4
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap)
        assert(eMaps.length == 1); val eMap = eMaps(0)
        assert(emptyMap(eMap(1)))
        if(n == N1)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N4), (N2,N5), (N3,N6))))
        else if(n == N2)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N4), (N3,N6))))
        else if(n == N3)
          assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N4))))
        else
          assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N7))))
      }
      // Secondary result-defining maps: N0 -> N0, N1 -> N2, N2 -> N4 or -1
      for(n <- List(N4,-1)){
        val rdMap: RemappingMap = Array(Array(N0,N2,n,-1), Array())
        assert(testHooks.findLinkages(unifs, rdMap) == List( (0,0) ))
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
      }
    }

    { // With unification of Nd_A,s
      val unifs1: UnificationList = List((0,1))
      val oaBitMap = Array(mkOABitMap(4,List(N2,N4)), mkOABitMap(0,List()))
      val map1List = List((N0,N0), (N1,N1), (N2,N3))
      // N0 -> N0, N1 -> N1, N2 -> N3, N3 -> N2, N4 or -1
      for(n <- List(N2,N4,-1)){
        val rdMap: RemappingMap = Array(Array(N0,N1,N3,n), Array())
        assert(testHooks.findLinkages(unifs1, rdMap).isEmpty)
        assert(testHooks.findLinkagesC(unifs1, rdMap).isEmpty)

        val eMaps = testHooks.makeExtensions(unifs1,oaBitMap,rdMap)
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
      val oaBitMap = Array(mkOABitMap(4,List(N5)), mkOABitMap(0,List()))

      // N0 -> N0 and N1/N2/N3/nothing -> N5
      val rdMap: RemappingMap = Array(Array(N0,-1,-1,-1), Array())
      assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
      assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
      for(n <- List(N1,N2,N3)){
        val rdMap: RemappingMap = Array(Array(N0,-1,-1,-1), Array())
        rdMap(0)(n) = N5
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap)
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
      val oaBitMap = Array(mkOABitMap(4,List(N2,N4,N5)), mkOABitMap(0,List()))
      // N0 -> N0, N1 -> N1, N2 -> N3, N3 -> N2/N4/N5/-1
      for(n <- List(N2,N4,N5,-1)){
        val rdMap: RemappingMap = Array(Array(N0,N1,N3,n), Array())
        val linkages = testHooks.findLinkages(unifs, rdMap)
        if(rdMap(0)(N3) == N2)  // linkage Nd_B -> Nd_B via N3 -> N2
          assert(linkages.sorted == List((1,2)))
        else assert(linkages.isEmpty)
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        val map1List = List((N0,N0), (N1,N1), (N2,N3), (N3,if(n >= 0) n else N6))
        val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap)
        assert(eMaps.length == 1); val eMap = eMaps(0)
        assert(checkMap(eMap(0), map1List) && emptyMap(eMap(1)))
      }
    }

    { // unify the Nd_B's
      val unifs = List((1,2))
      val oaBitMap = Array(mkOABitMap(4,List(N5)), mkOABitMap(0,List()))
      // N0 -> N0, N1 -> N5/-, N2 -> N2, N3 -> N4
      for(n <- List(N5,-1)){
        val rdMap: RemappingMap = Array(Array(N0,n,N2,N4), Array())
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        val map1List = List((N0,N0), (N1,if(n >= 0) n else N6), (N2,N2), (N3,N4))
        val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap)
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

    { // No unifications
      val unifs: UnificationList = List()
      val oaBitMap = Array(mkOABitMap(4,List(N4)), mkOABitMap(1,List()))
      // N0 -> N0, N1/N2/N3/- -> N4
      val rdMap : RemappingMap = Array(Array(N0,-1,-1,-1), Array(-1))
      assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
      assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
      for(n <- List(N1,N2,N3)){
        val rdMap : RemappingMap = Array(Array(N0,-1,-1,-1), Array(-1))
        rdMap(0)(n) = N4
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)

        val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap)
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

    { // Unify the Nd_A's
      val unifs: UnificationList = List((1,1))
      val oaBitMap = Array(mkOABitMap(4,List(N2,N4)), mkOABitMap(1,List()))
      // N0 -> N0, N1 -> N1, N2 -> N2/N4/-, N3 -> N3
      for(n <- List(N2,N4,-1)){
        val rdMap : RemappingMap = Array(Array(N0,N1,n,N3), Array(-1))
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        val linkagesC = testHooks.findLinkagesC(unifs, rdMap)
        if(n == N2)  // Common missing component with id N2
          assert(linkagesC == List((0,0)))
        else assert(linkagesC.isEmpty)

        val map1List = List((N0,N0), (N1,N1), (N3,N3))
/* case n == N2
            // FIXME I'm not sure following is correct
            val extendedMaps = testHooks.extendForLinkages(rdMap, linkagesC)
            // rdMap is already defined on N1,N2; can't map T0 -> T0 
            assert(extendedMaps.length == 1); val eMap = extendedMaps(0)
            //println(Remapper.show(eMap))
            assert(checkMap(eMap(0), (N2,N2)::map1List))
            assert(emptyMap(eMap(1)))
FIXME: test makeExtensions here
  case n != N2
            val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap)
            assert(eMaps.length == 1); val eMap = eMaps(0)
            if(n == N4) assert(checkMap(eMap(0), (N2,N4)::map1List))
            else assert(xx < 0 && checkMap(eMap(0), (N2,N5)::map1List))



 */
        

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

      val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap)
      val map1List = List((N0,N0))
      //println("****"+Remapper.show(rdMap1))
      //for(eMap <- eMaps) println(Remapper.show(eMap))
      if(n == N2){
        assert(eMaps.length == 1); val eMap = eMaps(0)
        // Map T0 to fresh value
        assert(checkMap(eMap(0), (N1,N2)::map1List) &&
          checkMap(eMap(1), List((T0,T1))))
      }
      else{
        assert(eMaps.length == 2 && eMaps.forall(eMap => 
          checkMap(eMap(1), List((T0,T1))) &&
            List(N1,N3).exists(n => checkMap(eMap(0), (N1,n)::map1List))))
// Doesn't give N1 -> N1 version
      }
      
    }
  }

  def apply() = {
    singleRef = true
    println("===RemappingExtenderTest===")
    test1; test2; test3; test4; test5
  }

}
