package ViewAbstraction

import RemapperP._

object SingleRefEffectOnUnificationTest{
  import TestStates._
  import TestUtils._

  private def mkUnifs(pre: Concretization, cv: ComponentView) = 
    Unification.allUnifs(
      pre.servers.remappingMap(cv.getParamsBound), pre.components, cv.components)

  /** Test based on (servers(N0); Th(T0,N1), Nd_A(N1,N2)) -> 
    *     (servers(N1); Th'(T0,N1), Nd_A(N1,N2)
    * acting on (servers(N0), Nd_B(N1,N2), Nd_C(N2,Null)).  */
  def test1 = {
    val pre = new Concretization(servers3(N0), 
      Array(initNodeSt(T0,N1), aNode(N1,N2)))
    val post = new Concretization(servers3(N1), 
      Array(pushSt(T0,N1), aNode(N1,N2)))
    val cv = new ComponentView(servers3(N0), Array(bNode(N1,N2), cNode(N2,Null)))
    val allUnifs = mkUnifs(pre, cv); assert(allUnifs.length == 1)
    val sreou = new SingleRefEffectOnUnification(pre, post, cv)
    val testHooks = sreou.TestHooks

    for((map1,unifs) <- allUnifs){
      assert(unifs.isEmpty)
      val otherArgs = testHooks.mkOtherArgs(map1, unifs)
      assert(otherArgs(0) == List(N1) && otherArgs(1).isEmpty)
      assert(checkMap(map1(0), List((N0,N0))) && emptyMap(map1(1)))
      val rdMaps = testHooks.extendMap(map1,otherArgs)
      // Can't map either N1 or N2 to N1, since all are ids
      assert(rdMaps.length == 1 && checkMap(rdMaps(0)(0), List((N0,N0))) && 
        emptyMap(rdMaps(0)(1)) )
      for(rdMap <- rdMaps){
        val linkages = testHooks.findLinkages(unifs, map1, rdMap)
        assert(linkages.isEmpty)
        // println(Remapper.show(rdMap)+" -> "+linkages.mkString(", "))
      }
    }
  }

  /* Test based on (fixed(N0); Th(T0, N1, N2), Nd_A(N1, N3)) ->
   *  (fixed(N4); Th'(T0, N1, N2), Nd_C(N1, N2)),
   * acting on (fixed(N0); Nd_A(N1, N2), Nd_B(N2, N3)).
   */
  def test2 = {
    val pre = new Concretization(servers3(N0), 
      Array(getDatumSt(T0, N1, N2), aNode(N1, N3)))
    val post = new Concretization(servers3(N4),
      Array(getDatumSt(T0, N1, N2), cNode(N1, N2)))
    val cv = new ComponentView(servers3(N0), Array(aNode(N1, N2), bNode(N2, N3)))
    val allUnifs = mkUnifs(pre, cv); assert(allUnifs.length == 2)
    val sreou = new SingleRefEffectOnUnification(pre, post, cv)
    val testHooks = sreou.TestHooks

    for((map1,unifs) <- allUnifs){
      if(unifs.isEmpty){
        val otherArgs = testHooks.mkOtherArgs(map1, unifs)
        // Just N4, from post.servers
        assert(otherArgs(0) == List(N4) && otherArgs(1).isEmpty)
        assert(checkMap(map1(0), List((N0,N0))) && emptyMap(map1(1)))
        val rdMaps = testHooks.extendMap(map1,otherArgs)
        // Map any of (N1, N2, N3, none) to N4
        assert(rdMaps.length == 4 &&
          rdMaps.forall(map2 => (
            checkMap(map2(0), List((N0,N0))) || 
              List(N1,N2,N3).exists(n => 
                checkMap(map2(0), List((N0,N0), (n,N4))))
          ) && emptyMap(map2(1))))
        for(rdMap <- rdMaps){
          val linkages = testHooks.findLinkages(unifs, map1, rdMap)
          assert(linkages.isEmpty)
          // println(Remapper.show(rdMap)+" -> "+linkages.mkString(", "))
        }
      }
      else{
        // unify the Nd_A's
        val map1List = List((N0,N0), (N1,N1), (N2,N3))
        assert(unifs == List((0,1)) && checkMap(map1(0), map1List) && 
          emptyMap(map1(1)) )
        val otherArgs = testHooks.mkOtherArgs(map1, unifs)
        // N4 from post.servers; N2 from the post-state of the unified component
        assert(otherArgs(0).sorted == List(N2,N4) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendMap(map1,otherArgs)
        // Can map N3 to (N2, N4 or none)
        assert(rdMaps.length == 3 &&
          rdMaps.forall(map2 =>
            List(N2,N4,-1).exists(n => checkMap(map2(0), (N3,n)::map1List)) &&
              emptyMap(map2(1)) ))
        for(rdMap <- rdMaps){
          val linkages = testHooks.findLinkages(unifs, map1, rdMap)
          // All linkages involve a unified component
          // println(Remapper.show(rdMap)+" -> "+linkages.mkString(", "))
          assert(linkages.isEmpty)
        }
      }
    }
  }

  /* Test based on (fixed(N0); Th(T0, N1, N2), Nd_A(N1, N3), Nd_B(N_2,N_4)) ->
   *  (fixed(N5); Th'(T0, N1, N2), Nd_C(N1, N2), Nd_B(N_2,N_4)),
   * acting on (fixed(N0); Nd_A(N1, N2), Nd_B(N2, N3)).
   */
  def test3 = {
    val pre = new Concretization(servers3(N0), 
      Array(getDatumSt(T0, N1, N2), aNode(N1, N3), bNode(N2,N4)))
    val post = new Concretization(servers3(N5),
      Array(getDatumSt(T0, N1, N2), cNode(N1, N2), bNode(N2,N4)))
    val cv = new ComponentView(servers3(N0), Array(aNode(N1, N2), bNode(N2, N3)))
    val allUnifs = mkUnifs(pre, cv); assert(allUnifs.length == 3)
    val sreou = new SingleRefEffectOnUnification(pre, post, cv)
    val testHooks = sreou.TestHooks

    for((map1,unifs) <- allUnifs){
      if(unifs.isEmpty){
        val map1List = List((N0,N0))
        assert(checkMap(map1(0), map1List) && emptyMap(map1(1)))
        val otherArgs = testHooks.mkOtherArgs(map1, unifs)
        // Just N5, from post.servers
        assert(otherArgs(0) == List(N5) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendMap(map1,otherArgs)
        // Map any of (N1,N2,N3,none) to N5
        // println(rdMaps.map(Remapper.show).mkString("\n"))
        assert(rdMaps.length == 4 &&
          rdMaps.forall(map2 => (
            checkMap(map2(0), map1List) ||
              List(N1,N2,N3).exists(n => checkMap(map2(0), (n,N5)::map1List))
          ) && emptyMap(map2(1)) ))
        for(rdMap <- rdMaps){
          val linkages = testHooks.findLinkages(unifs, map1, rdMap)
          assert(linkages.isEmpty)
          // println(Remapper.show(rdMap)+" -> "+linkages.mkString(", "))
        }
      }
      else if(unifs == List((0,1))){ // unify the Nd_A's
        val map1List = List((N0,N0), (N1,N1), (N2,N3))
        assert(checkMap(map1(0), map1List) && emptyMap(map1(1)))
        val otherArgs = testHooks.mkOtherArgs(map1, unifs)
        // N5 from post.servers; N2 from the post-state of the Nd_A; N4 from
        // the post-state of the Nd_B (acquired reference).
        assert(otherArgs(0).sorted == List(N2,N4,N5) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendMap(map1,otherArgs)
        // Map N3 to any of (N2,N4,N5,none)
        // println(rdMaps.map(Remapper.show).mkString("\n"))
        assert(rdMaps.length == 4 &&
          rdMaps.forall(map2 => (
            checkMap(map2(0), map1List) ||
              List(N2,N4,N5,-1).exists(n => checkMap(map2(0), (N3,n)::map1List))
          ) && emptyMap(map2(1)) ))
        for(rdMap <- rdMaps){
          val linkages = testHooks.findLinkages(unifs, map1, rdMap)
          // println(Remapper.show(rdMap)+" -> "+linkages.mkString(", "))
          if(rdMap(0)(N3) == N2)  // linkage Nd_B -> Nd_B via N3 -> N2
            assert(linkages.sorted == List((1,2,N2)))
          else assert(linkages.isEmpty)
        }

      }
      else{ // unify the Nd_B's
        val map1List = List((N0,N0), (N2,N2), (N3,N4))
        assert(unifs == List((1,2)) && checkMap(map1(0), map1List) && 
          emptyMap(map1(1)))
        val otherArgs = testHooks.mkOtherArgs(map1, unifs)
        // Just N5 from post.servers
        assert(otherArgs(0) == List(N5) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendMap(map1,otherArgs)
        // println(rdMaps.map(Remapper.show).mkString("\n"))
        // Map N1 to N5 or nothing
        assert(rdMaps.length == 2 && 
          rdMaps.forall(map2 => 
            List(N5,-1).exists(n => checkMap(map2(0), (N1,n)::map1List)) &&
              emptyMap(map2(1)) ))
        for(rdMap <- rdMaps){
          val linkages = testHooks.findLinkages(unifs, map1, rdMap)
          println(Remapper.show(rdMap)+" -> "+linkages.mkString(", "))
          assert(linkages.isEmpty)
        }
      }
    }
  }


  def apply() = {
    singleRef = true
    println("===SingleRefEffectOnUnificationTest===")
    test1; test2; test3
    singleRef = false
  }


}
