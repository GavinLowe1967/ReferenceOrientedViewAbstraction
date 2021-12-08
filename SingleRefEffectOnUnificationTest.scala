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
      val rdMaps = testHooks.extendToRDMap(map1,otherArgs)
      // Can't map either N1 or N2 to N1, since all are ids
      assert(rdMaps.length == 1)
      for(rdMap <- rdMaps){
        assert(checkMap(rdMap(0), List((N0,N0))) && emptyMap(rdMap(1)))
        assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
        val repMaps = testHooks.extendMapping(unifs, rdMap)
        assert(repMaps.length == 1); val repMap = repMaps(0)
        assert(checkMap(repMap(0), List((N0,N0),(N1,N3),(N2,N4))) && 
          emptyMap(repMap(1)))
      }
      // No secondaries
      assert(testHooks.getSecondaryInfo(map1).isEmpty)
    } // end of for loop

    // Secondary induced transitions
    assert(testHooks.acquiredRefs.isEmpty)

    // Overall result
    val (result,result1) = sreou()
    // println(result.map(tuple => StateArray.show(tuple._2)).mkString("\n"))
    assert(result.length == 1 && 
      result(0)._2.sameElements(Array(bNode(N3,N4), cNode(N4,Null))))
  }

  /* Test based on (fixed(N0); Th(T0, N1, N2), Nd_A(N1, N3)) ->
   *  (fixed(N4); Th'(T0, N1, N2), Nd_C(N1, N2)),
   * acting on (fixed(N0); Nd_A(N1, N2), Nd_B(N2, N3)).
   */
  def test2 = {
    println("=test2=")
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
        val rdMaps = testHooks.extendToRDMap(map1,otherArgs)
        // Map any of (N1, N2, N3, none) to N4
        assert(rdMaps.length == 4 &&
          rdMaps.forall(map2 => (
            checkMap(map2(0), List((N0,N0))) || 
              List(N1,N2,N3).exists(n => 
                checkMap(map2(0), List((N0,N0), (n,N4))))
          ) && emptyMap(map2(1))))
        for(rdMap <- rdMaps){
          assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
          val repMaps = testHooks.extendMapping(unifs, rdMap)
          assert(repMaps.length == 1); val repMap = repMaps(0)
          // Maps all other params to fresh params
          assert(emptyMap(repMap(1)))
          if(rdMap(0)(N1) == N4) 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N4), (N2,N5), (N3,N6))))
          else if(rdMap(0)(N2) == N4) 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N5), (N2,N4), (N3,N6))))
          else if(rdMap(0)(N3) == N4) 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N4))))
          else 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N7))))
        } // end of inner for

        // Secondary info; link from the Nd_C
        val secondaryInfo = testHooks.getSecondaryInfo(map1)
        assert(secondaryInfo.length == 1); val (map2,sc) = secondaryInfo(0)
        assert(sc == post.components(1) && 
          checkMap(map2(0), List((N0,N0), (N1,N2))) && emptyMap(map2(1)))
        val otherArgs1 = testHooks.mkSecondaryOtherArgsMap(map2, sc) 
        // println("otherArgs1 = "+otherArgs1.mkString("; "))
        // N4 from post.fixed; N1 from sc
        assert(otherArgs1(0).sorted == List(N1,N4) && otherArgs1(1).isEmpty)
        val rdsMaps = testHooks.extendToRDMap(map2,otherArgs1)
        println(rdsMaps.map(Remapper.show).mkString("\n"))

      } // end of no unifications case
      else{
        // unify the Nd_A's
        val map1List = List((N0,N0), (N1,N1), (N2,N3))
        assert(unifs == List((0,1)) && checkMap(map1(0), map1List) && 
          emptyMap(map1(1)) )
        val otherArgs = testHooks.mkOtherArgs(map1, unifs)
        // N4 from post.servers; N2 from the post-state of the unified component
        assert(otherArgs(0).sorted == List(N2,N4) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,otherArgs)
        // Can map N3 to (N2, N4 or none)
        assert(rdMaps.length == 3 &&
          rdMaps.forall(map2 =>
            List(N2,N4,-1).exists(n => checkMap(map2(0), (N3,n)::map1List)) &&
              emptyMap(map2(1)) ))
        for(rdMap <- rdMaps){
          val linkages = testHooks.findLinkages(unifs, rdMap)
          // All linkages involve a unified component
          assert(linkages.isEmpty)
          val repMaps = testHooks.extendMapping(unifs, rdMap)
          assert(repMaps.length == 1); val repMap = repMaps(0)
          // N3 should map to yy
          val xx = rdMap(0)(N3); val yy = if(xx >= 0) xx else N5
          assert(checkMap(repMap(0), (N3,yy)::map1List) && emptyMap(repMap(1)))
          // No secondaries: prevented by unification
          assert(testHooks.getSecondaryInfo(map1).isEmpty)
        }
      } // end of unifying Nd_A's case
    } // end of for(... <- allUnifs)

    // Secondary induced transitions
    assert(testHooks.acquiredRefs == List((1,(0,N2))))

    // Check top-level result
    val (result,result1) = sreou()
    val expected = List(
      // with empty unifs
      Array(aNode(N4,N5), bNode(N5,N6)), Array(aNode(N5,N4), bNode(N4,N6)),
      Array(aNode(N5,N6), bNode(N6,N4)), Array(aNode(N5,N6), bNode(N6,N7)),
      // unify the Nd_A's
      Array(aNode(N1,N3), bNode(N3,N2)), Array(aNode(N1,N3), bNode(N3,N4)),
      Array(aNode(N1,N3), bNode(N3,N5))
    )
    assert(result.length == expected.length)
    for(exp <- expected) 
      assert(result.exists(tuple => exp.sameElements(tuple._2)))
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
        val rdMaps = testHooks.extendToRDMap(map1,otherArgs)
        // Map any of (N1,N2,N3,none) to N5
        assert(rdMaps.length == 4 &&
          rdMaps.forall(map2 => (
            checkMap(map2(0), map1List) ||
              List(N1,N2,N3).exists(n => checkMap(map2(0), (n,N5)::map1List))
          ) && emptyMap(map2(1)) ))
        for(rdMap <- rdMaps){
          assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
          val repMaps = testHooks.extendMapping(unifs, rdMap)
          assert(repMaps.length == 1); val repMap = repMaps(0)
          // Maps all other params to fresh params
          assert(emptyMap(repMap(1)))
          if(rdMap(0)(N1) == N5) 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N7))))
          else if(rdMap(0)(N2) == N5) 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N6), (N2,N5), (N3,N7))))
          else if(rdMap(0)(N3) == N5) 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N6), (N2,N7), (N3,N5))))
          else 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N6), (N2,N7), (N3,N8))))
        }
      }
      else if(unifs == List((0,1))){ // unify the Nd_A's
        val map1List = List((N0,N0), (N1,N1), (N2,N3))
        assert(checkMap(map1(0), map1List) && emptyMap(map1(1)))
        val otherArgs = testHooks.mkOtherArgs(map1, unifs)
        // N5 from post.servers; N2 from the post-state of the Nd_A; N4 from
        // the post-state of the Nd_B (acquired reference).
        assert(otherArgs(0).sorted == List(N2,N4,N5) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,otherArgs)
        // Map N3 to any of (N2,N4,N5,none)
        assert(rdMaps.length == 4 &&
          rdMaps.forall(map2 => emptyMap(map2(1)) && 
            List(N2,N4,N5,-1).exists(n => checkMap(map2(0), (N3,n)::map1List))))
        for(rdMap <- rdMaps){
          val linkages = testHooks.findLinkages(unifs, rdMap)
          if(rdMap(0)(N3) == N2)  // linkage Nd_B -> Nd_B via N3 -> N2
            assert(linkages.sorted == List((1,2,N2))) 
          else assert(linkages.isEmpty)
          // Each representative map extends the corresponding result-defining
          // map, maybe mapping undefined N3 to fresh N6
          val repMaps = testHooks.extendMapping(unifs, rdMap)
          assert(repMaps.length == 1); val repMap = repMaps(0)
          // N3 should map to yy
          val xx = rdMap(0)(N3); val yy = if(xx >= 0) xx else N6
          assert(checkMap(repMap(0), (N3,yy)::map1List) && emptyMap(repMap(1)))
        }
      }
      else{ // unify the Nd_B's
        val map1List = List((N0,N0), (N2,N2), (N3,N4))
        assert(unifs == List((1,2)) && checkMap(map1(0), map1List) && 
          emptyMap(map1(1)))
        val otherArgs = testHooks.mkOtherArgs(map1, unifs)
        // Just N5 from post.servers
        assert(otherArgs(0) == List(N5) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,otherArgs)
        // Map N1 to N5 or nothing
        assert(rdMaps.length == 2 && 
          rdMaps.forall(map2 => emptyMap(map2(1)) &&
            List(N5,-1).exists(n => checkMap(map2(0), (N1,n)::map1List))))
        for(rdMap <- rdMaps){
          assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
          val repMaps = testHooks.extendMapping(unifs, rdMap)
          // println(repMaps.map(Remapper.show).mkString("\n"))
          assert(repMaps.length == 1); val repMap = repMaps(0)
          // N1 should map to yy
          val xx = rdMap(0)(N1); val yy = if(xx >= 0) xx else N6
          assert(checkMap(repMap(0), (N1,yy)::map1List) && emptyMap(repMap(1)))
        }
      } // end of unifying Nd_B's case
      // No secondary transitions, since mapping N1 to N2 requires unifying
      // Nd_A(N1) with Nd_B(N_2)
      assert(testHooks.getSecondaryInfo(map1).isEmpty)
    } // end of outer for loop

    // Secondary induced transitions; but not achievable
    assert(testHooks.acquiredRefs == List((1,(0,N2))))

    // Check top-level result
    val (result,result1) = sreou()
    // println(result.map(tuple => StateArray.show(tuple._2)).mkString("\n"))
    val expected = List(
      // With empty unifs
      Array(aNode(N5, N6), bNode(N6, N7)), Array(aNode(N6, N5), bNode(N5, N7)),
      Array(aNode(N6, N7), bNode(N7, N5)), Array(aNode(N6, N7), bNode(N7, N8)),
      // unify the Nd_A's
      Array(aNode(N1, N3), bNode(N3, N2)), Array(aNode(N1, N3), bNode(N3, N4)),
      Array(aNode(N1, N3), bNode(N3, N5)), Array(aNode(N1, N3), bNode(N3, N6)),
      // unify the Nd_B's
      Array(aNode(N5, N2), bNode(N2, N4)), Array(aNode(N6, N2), bNode(N2, N4))
    )
    assert(result.length == expected.length)
    for(exp <- expected) 
      assert(result.exists(tuple => exp.sameElements(tuple._2)))
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
    val allUnifs = mkUnifs(pre, cv); assert(allUnifs.length == 3)
    // println(allUnifs.map(_._2).mkString("\n"))

    val sreou = new SingleRefEffectOnUnification(pre, post, cv)
    val testHooks = sreou.TestHooks

    for((map1,unifs) <- allUnifs){
      if(unifs.isEmpty){
        val map1List = List((N0,N0))
        assert(checkMap(map1(0), map1List) && emptyMap(map1(1)))
        val otherArgs = testHooks.mkOtherArgs(map1, unifs)
        assert(otherArgs(0) == List(N4) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,otherArgs)
        // Map any of (N1,N2,N3,none) to N4
        assert(rdMaps.length == 4) 
        for(map2 <- rdMaps) assert(
          emptyMap(map2(1)) &&
            (checkMap(map2(0), map1List) ||
              List(N1,N2,N3).exists(n => checkMap(map2(0), (n,N4)::map1List))))
        for(rdMap <- rdMaps){
          assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
          val repMaps = testHooks.extendMapping(unifs, rdMap)
          assert(repMaps.length == 1); val repMap = repMaps(0)
          // Maps all other params to fresh params
          assert(checkMap(repMap(1), List((T0,T1))))
          if(rdMap(0)(N1) == N4)
            assert(checkMap(repMap(0), List((N0,N0), (N1,N4), (N2,N5), (N3,N6))))
          else if(rdMap(0)(N2) == N4) 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N5), (N2,N4), (N3,N6))))
          else if(rdMap(0)(N3) == N4) 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N4))))
          else 
            assert(checkMap(repMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N7))))
        }
      }
      else if(unifs == List((1,1))){ // unify the Nd_A's
        val map1List = List((N0,N0), (N1,N1), (N3,N3))
        assert(checkMap(map1(0), map1List) && emptyMap(map1(1)))
        val otherArgs = testHooks.mkOtherArgs(map1, unifs)
        assert(otherArgs(0).sorted == List(N2,N4) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,otherArgs)
        // Map N2 to any of (N2,N4,none)
        assert(rdMaps.length == 3 &&
          rdMaps.forall(map2 => emptyMap(map2(1)) &&
            List(N2,N4,-1).exists(n => checkMap(map2(0), (N2,n)::map1List))))
        for(rdMap <- rdMaps){
          val xx = rdMap(0)(N2) // Note: gets overwritten
          val linkages = testHooks.findLinkages(unifs, rdMap)
          val repMaps = testHooks.extendMapping(unifs, rdMap)
          assert(repMaps.length == 1); val repMap = repMaps(0)
          assert(checkMap(repMap(1), List((T0,T1)))) // fresh value
          if(xx == N2){  // Common missing component with id N2
            assert(linkages == List((0,0,2)))
            val extendedMaps = testHooks.extendForLinkages(rdMap, linkages)
            // rdMap is already defined on N1,N2; can't map T0 -> T0 
            assert(extendedMaps.length == 1); val eMap = extendedMaps(0)
            assert(checkMap(eMap(0), (N2,N2)::map1List) && emptyMap(eMap(1)))
            // Extension maps T0 -> T1
            assert(checkMap(repMap(0), (N2,N2)::map1List))
          }
          else{
            assert(linkages.isEmpty)
            if(xx == N4) assert(checkMap(repMap(0), (N2,N4)::map1List))
            else assert(xx < 0 && checkMap(repMap(0), (N2,N5)::map1List))
          }
        }
      }
      else{
        // Both components unified, which recreates the former transition
        assert(unifs.sorted == List((0,0), (1,1)))
        assert(!testHooks.isSufficientUnif(unifs))
      }
      // No secondaries: cv.principal has the wrong type
      assert(testHooks.getSecondaryInfo(map1).isEmpty)
    } // end of for loop

    // Secondary induced transitions
    assert(testHooks.acquiredRefs.isEmpty) // wrong type

    // Check overall result
    val (result,result1) = sreou()
    val expected = List(
      // No unifs
      Array(getDatumSt(T1,N4,N5), aNode(N4,N6)),
      Array(getDatumSt(T1,N5,N4), aNode(N5,N6)),
      Array(getDatumSt(T1,N5,N6), aNode(N5,N4)),
      Array(getDatumSt(T1,N5,N6), aNode(N5,N7)),
      // Unify the Nd_A's
      Array(getDatumSt(T1,N1,N2), aNode(N1,N3)),
      Array(getDatumSt(T1,N1,N4), aNode(N1,N3)),
      Array(getDatumSt(T1,N1,N5), aNode(N1,N3)),
    )
    assert(result.length == expected.length)
    for(exp <- expected) 
      assert(result.exists(tuple => exp.sameElements(tuple._2)))
  }


  /** Test based on (fixed(N0); Th(T0, N1), Nd_A(N1,N0)) ->
    *   (fixed(N2); Th'(T0), Nd_A(N1,N0))
    * acting on  (fixed(N0); Th''(T0, N0), Nd_B(N0,N1)). */
  def test5 = {
    val pre = new Concretization(servers3(N0), 
      Array(pushSt(T0, N1), aNode(N1, N0)))
    val post = new Concretization(servers3(N2), Array(unlock(T0), aNode(N1, N0)))
    val cv = new ComponentView(servers3(N0), 
      Array(setTopB(T0, N0), bNode(N0, N1)))
    val sreou = new SingleRefEffectOnUnification(pre, post, cv)
    val testHooks = sreou.TestHooks

    val allUnifs = mkUnifs(pre, cv); assert(allUnifs.length == 1)
    //println(allUnifs.map(_._2).mkString("\n"))
    val (map1,unifs) = allUnifs(0); val map1List = List((N0,N0))
    assert(unifs.isEmpty && checkMap(map1(0), map1List) && emptyMap(map1(1)))
    val otherArgs = testHooks.mkOtherArgs(map1, unifs)
    // Just N2 from post.fixed
    assert(otherArgs(0) == List(N2) && otherArgs(1).isEmpty)
    val rdMaps = testHooks.extendToRDMap(map1,otherArgs)
    // is map2 N0->N0, N1->n ?
    def isMap(map2: RemappingMap, n: Int) = 
      emptyMap(map2(1)) && checkMap(map2(0), (N1,n)::map1List)
    // Map N1 to N2 or not
    assert(rdMaps.length == 2 &&
      rdMaps.forall(map2 => List(N2,-1).exists(n => isMap(map2,n))))
    for(rdMap <- rdMaps){
      val xx = rdMap(0)(N1) // gets overwritten
      val linkages = testHooks.findLinkages(unifs, rdMap)
      // linkage Nd_A -> Nd_B on N0 (whether N1 maps to N0 or not)
      assert(linkages == List((1,1,0))) 
      val extendedMaps = testHooks.extendForLinkages(rdMap, linkages)
      val repMaps = testHooks.extendMapping(unifs, rdMap)
      if(xx == N2){
        // rdMap already total on params of Nd_B 
        assert(extendedMaps.length == 1 && isMap(extendedMaps(0), N2))
        assert(repMaps.length == 1); val repMap = repMaps(0)
        // Map T0 to fresh value
        assert(checkMap(repMap(0), (N1,N2)::map1List) &&
          checkMap(repMap(1), List((T0,T1))))
      }
      else{
        assert(xx < 0)
        // Can map N1 to N1 or not
        assert(extendedMaps.length == 2 &&
          extendedMaps.forall(eMap => List(N1,-1).exists(n => isMap(eMap,n))))
        // N1 maps to N1 or fresh value
        assert(repMaps.length == 2 && repMaps.forall(repMap => 
          checkMap(repMap(1), List((T0,T1))) &&
            List(N1,N3).exists(n => checkMap(repMap(0), (N1,n)::map1List))))
      }
    } // end of for loop

    // Secondary induced transitions
    assert(testHooks.getSecondaryInfo(map1).isEmpty)
    assert(testHooks.acquiredRefs.isEmpty)

    // Check overall result
    val (result,result1) = sreou()
    val expected = List(
      Array(setTopB(T1,N0), bNode(N0,N2)), Array(setTopB(T1,N0), bNode(N0,N1)),
      Array(setTopB(T1,N0), bNode(N0,N3)),
    )
    assert(result.length == expected.length)
    for(exp <- expected) 
      assert(result.exists(tuple => exp.sameElements(tuple._2)))
  }

  /** Main function. */
  def apply() = {
    singleRef = true
    println("===SingleRefEffectOnUnificationTest===")
    test1; test2; test3; test4; test5
    singleRef = false
  }


}
