package ViewAbstraction


object RemappingExtenderTest{

  import TestStates._
  import TestUtils._
  import Unification.UnificationList // = List[(Int,Int)]

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
    val unifs: UnificationList = List()
    // N0 -> N0, one of N1,N2,N3 -> N4
    for(n <- List(N1,N2,N3)){
      val rdMap: RemappingMap = Array(Array(N0,-1,-1,-1), Array())
      rdMap(0)(n) = N4
      assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
      assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
    }
    // Secondary result-defining maps: N0 -> N0, N1 -> N2, N2 -> N4 or -1
    for(n <- List(N4,-1)){
      val rdMap: RemappingMap = Array(Array(N0,N2,n,-1), Array())
      assert(testHooks.findLinkages(unifs, rdMap) == List( (0,0) ))
      assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
    }
    // With unification of Nd_A,s
    val unifs1: UnificationList = List((0,1))
    // N0 -> N0, N1 -> N1, N2 -> N3, N3 -> N2, N4 or -1
    for(n <- List(N2,N4,-1)){
      val rdMap: RemappingMap = Array(Array(N0,N1,N3,n), Array())
      assert(testHooks.findLinkages(unifs1, rdMap).isEmpty)
      assert(testHooks.findLinkagesC(unifs1, rdMap).isEmpty)
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

    // No unification
    val unifs: UnificationList = List()
    // N0 -> N0 and N1/N2/N3/nothing -> N5
    val rdMap: RemappingMap = Array(Array(N0,-1,-1,-1), Array())
    assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
    assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
    for(n <- List(N1,N2,N3)){
      val rdMap: RemappingMap = Array(Array(N0,-1,-1,-1), Array())
      rdMap(0)(n) = N5
      assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
      assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
    }

    // Unify the Nd_A's
    val unifs1: UnificationList = List((0,1))
    // N0 -> N0, N1 -> N1, N2 -> N3, N3 -> N2/N4/N5/-1
    for(n <- List(N2,N4,N5,-1)){
      val rdMap: RemappingMap = Array(Array(N0,N1,N3,n), Array())
      val linkages = testHooks.findLinkages(unifs1, rdMap)
      if(rdMap(0)(N3) == N2)  // linkage Nd_B -> Nd_B via N3 -> N2
        assert(linkages.sorted == List((1,2)))
      else assert(linkages.isEmpty)
      assert(testHooks.findLinkagesC(unifs1, rdMap).isEmpty)
    }

    // unify the Nd_B's
    val unifs2 = List((1,2))
    // N0 -> N0, N1 -> N5/-, N2 -> N2, N3 -> N4
    for(n <- List(N5,-1)){
      val rdMap: RemappingMap = Array(Array(N0,n,N2,N4), Array())
      assert(testHooks.findLinkages(unifs2, rdMap).isEmpty)
      assert(testHooks.findLinkagesC(unifs2, rdMap).isEmpty)
    }

  }


  def apply() = {
    singleRef = true
    println("===RemappingExtenderTest===")
    test1; test2; test3
  }

}
