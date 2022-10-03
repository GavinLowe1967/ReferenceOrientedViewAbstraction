package ViewAbstraction

import RemapperP._
import scala.collection.mutable.ArrayBuffer

/** Test of SingleEffectOnUnification, part 2.  The tests are split into two
  * to keep things manageable. */
object SingleRefEffectOnUnificationTest2{
  import TestStates._
  import TestUtils._
  import Remapper.applyRemapping

  def mkTrans(pre: Concretization, post: Concretization) = 
    new Transition(pre,-1,post)


  def mkUnifs(pre: Concretization, cv: ComponentView) = 
    Unification.allUnifs(pre, cv) // .components)

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
    val sreou = new SingleRefEffectOnUnification(mkTrans(pre,post), cv)
    val testHooks = sreou.TestHooks

    for((map1,unifs) <- allUnifs){
      if(unifs.isEmpty){                                 // No unification
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
    // for(tuple <- result) println(StateArray.show(tuple._2)+"; "+tuple._3)
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
      assert(result.exists(tuple => {
        val states = applyRemapping(tuple._1, cv.components)
        exp.sameElements(states/*tuple._2*/)
      }))
    assert(result1.isEmpty)
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
    val sreou = new SingleRefEffectOnUnification(mkTrans(pre, post), cv)
    val testHooks = sreou.TestHooks

    val allUnifs = mkUnifs(pre, cv); assert(allUnifs.length == 1)
    //println(allUnifs.map(_._2).mkString("\n"))
    val (map1,unifs) = allUnifs(0); val map1List = List((N0,N0))
    assert(unifs.isEmpty && checkMap(map1(0), map1List) && emptyMap(map1(1)))
    val (otherArgs, oaBitMap) = testHooks.mkOtherArgs(map1, unifs)
    // Just N2 from post.fixed
    assert(otherArgs(0) == List(N2) && otherArgs(1).isEmpty)
    val rdMaps = testHooks.extendToRDMap(map1,oaBitMap)
    // Map N1 to N2 or not
    assert(rdMaps.length == 2 &&
      rdMaps.forall(map2 => emptyMap(map2(1)) && 
        List(N2,-1).exists(n => checkMap(map2(0), (N1,n)::map1List))))

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
      assert(result.exists(tuple => {
        val states = applyRemapping(tuple._1, cv.components)        
        exp.sameElements(states/*tuple._2*/)
      }))
    assert(result1.isEmpty)
  }

}
