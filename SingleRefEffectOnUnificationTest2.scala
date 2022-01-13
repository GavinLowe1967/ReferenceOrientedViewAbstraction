package ViewAbstraction

import RemapperP._
import scala.collection.mutable.ArrayBuffer

/** Test of SingleEffectOnUnification, part 2.  The tests are split into two
  * to keep things manageable. */
object SingleRefEffectOnUnificationTest2{
  import TestStates._
  import TestUtils._

  def mkUnifs(pre: Concretization, cv: ComponentView) = 
    Unification.allUnifs(
      pre.servers.remappingMap(cv.getParamsBound), pre.components, cv.components)

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
        val (otherArgs, oaBitMap) = testHooks.mkOtherArgs(map1, unifs)
        assert(otherArgs(0) == List(N4) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,oaBitMap)
        // Map any of (N1,N2,N3,none) to N4
        assert(rdMaps.length == 4) 
        for(map2 <- rdMaps) assert(
          emptyMap(map2(1)) &&
            (checkMap(map2(0), map1List) ||
              List(N1,N2,N3).exists(n => checkMap(map2(0), (n,N4)::map1List))))
        for(rdMap <- rdMaps){
          assert(testHooks.findLinkages(unifs, rdMap).isEmpty)
          assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
          val repMaps = testHooks.extendPrimaryMapping(unifs, oaBitMap, rdMap)
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

          val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap)
          assert(eMaps.length == 1); val eMap = eMaps(0)
          // Maps all other params to fresh params
          assert(checkMap(eMap(1), List((T0,T1))))
          if(rdMap(0)(N1) == N4)
            assert(checkMap(eMap(0), List((N0,N0), (N1,N4), (N2,N5), (N3,N6))))
          else if(rdMap(0)(N2) == N4) 
            assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N4), (N3,N6))))
          else if(rdMap(0)(N3) == N4) 
            assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N4))))
          else 
            assert(checkMap(eMap(0), List((N0,N0), (N1,N5), (N2,N6), (N3,N7))))
        }
      }
      else if(unifs == List((1,1))){ // unify the Nd_A's
        val map1List = List((N0,N0), (N1,N1), (N3,N3))
        assert(checkMap(map1(0), map1List) && emptyMap(map1(1)))
        val (otherArgs, oaBitMap) = testHooks.mkOtherArgs(map1, unifs)
        assert(otherArgs(0).sorted == List(N2,N4) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,oaBitMap)
        // Map N2 to any of (N2,N4,none)
        assert(rdMaps.length == 3 &&
          rdMaps.forall(map2 => emptyMap(map2(1)) &&
            List(N2,N4,-1).exists(n => checkMap(map2(0), (N2,n)::map1List))))
        for(rdMap <- rdMaps){
          val xx = rdMap(0)(N2) // Note: gets overwritten
          val linkagesB = testHooks.findLinkages(unifs, rdMap)
          val linkagesC = testHooks.findLinkagesC(unifs, rdMap)
          // Note: at one point the cloning below was necessary
          val repMaps = testHooks.extendPrimaryMapping(unifs, oaBitMap, rdMap/*.map(_.clone)*/)
          assert(repMaps.length == 1); val repMap = repMaps(0)
          assert(checkMap(repMap(1), List((T0,T1)))) // fresh value
          if(xx == N2){  // Common missing component with id N2
            assert(linkagesC == List((0,0)) && linkagesB.isEmpty)
/*
            // FIXME I'm not sure following is correct
            val extendedMaps = testHooks.extendForLinkages(rdMap, linkagesC)
            // rdMap is already defined on N1,N2; can't map T0 -> T0 
            assert(extendedMaps.length == 1); val eMap = extendedMaps(0)
            //println(Remapper.show(eMap))
            assert(checkMap(eMap(0), (N2,N2)::map1List))
            assert(emptyMap(eMap(1)))
FIXME: test makeExtensions here
 */
            // Extension maps T0 -> T1 (above)
            assert(checkMap(repMap(0), (N2,N2)::map1List))
          }
          else{
            assert(linkagesB.isEmpty && linkagesC.isEmpty)
            if(xx == N4) assert(checkMap(repMap(0), (N2,N4)::map1List))
            else assert(xx < 0 && checkMap(repMap(0), (N2,N5)::map1List))

            val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap)
            assert(eMaps.length == 1); val eMap = eMaps(0)
            if(xx == N4) assert(checkMap(eMap(0), (N2,N4)::map1List))
            else assert(xx < 0 && checkMap(eMap(0), (N2,N5)::map1List))
          }
        } // end of for loop 
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
    val (otherArgs, oaBitMap) = testHooks.mkOtherArgs(map1, unifs)
    // Just N2 from post.fixed
    assert(otherArgs(0) == List(N2) && otherArgs(1).isEmpty)
    val rdMaps = testHooks.extendToRDMap(map1,oaBitMap)
    // is map2 N0->N0, N1->n ?
    def isMap(map2: RemappingMap, n: Int) = 
      emptyMap(map2(1)) && checkMap(map2(0), (N1,n)::map1List)
    // Map N1 to N2 or not
    assert(rdMaps.length == 2 &&
      rdMaps.forall(map2 => List(N2,-1).exists(n => isMap(map2,n))))
    for(rdMap <- rdMaps){
      val rdMap1 = Remapper.cloneMap(rdMap) // clone since rdMap mutated
      val xx = rdMap(0)(N1) // gets overwritten
      val linkages = testHooks.findLinkages(unifs, rdMap)
      // linkage Nd_A -> Nd_B on N0 (whether N1 maps to N0 or not)
      assert(linkages == List((1,1))) 
      assert(testHooks.findLinkagesC(unifs, rdMap).isEmpty)
      val extendedMaps = testHooks.extendForLinkages(rdMap, oaBitMap, linkages)
      val repMaps = testHooks.extendPrimaryMapping(unifs, oaBitMap, rdMap)
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

      val eMaps = testHooks.makeExtensions(unifs,oaBitMap,rdMap1)
      //println("****"+Remapper.show(rdMap1))
      //for(eMap <- eMaps) println(Remapper.show(eMap))
      if(xx == N2){
        assert(eMaps.length == 1); val eMap = eMaps(0)
        // Map T0 to fresh value
        assert(checkMap(eMap(0), (N1,N2)::map1List) &&
          checkMap(eMap(1), List((T0,T1))))
      }
      else{
        assert(xx < 0)
        assert(eMaps.length == 2 && eMaps.forall(eMap => 
          checkMap(eMap(1), List((T0,T1))) &&
            List(N1,N3).exists(n => checkMap(eMap(0), (N1,n)::map1List))))
// Doesn't give N1 -> N1 version
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

}
