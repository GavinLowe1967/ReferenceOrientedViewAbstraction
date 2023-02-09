package ViewAbstraction

import RemapperP._
import scala.collection.mutable.ArrayBuffer

/** Test of SingleEffectOnUnification, part 1. */
object SingleRefEffectOnUnificationTest{
  import TestStates._
  import TestUtils._
  import SingleRefEffectOnUnificationTest2.{mkUnifs,test4,test5,mkTrans}
  import Remapper.applyRemapping

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
    val sreou = new SingleRefEffectOnUnification(mkTrans(pre, post), cv)
    val testHooks = sreou.TestHooks

    for((map1,unifs) <- allUnifs){
      assert(unifs.isEmpty)
      val (otherArgs, oaBitMap) = testHooks.mkOtherArgs(map1, unifs)
      assert(otherArgs(0) == List(N1) && otherArgs(1).isEmpty)
      assert(checkMap(map1(0), List((N0,N0))) && emptyMap(map1(1)))
      val rdMaps = testHooks.extendToRDMap(map1,oaBitMap)
      // Can't map either N1 or N2 to N1, since all are ids
      assert(rdMaps.length == 1); val rdMap = rdMaps(0)
      assert(checkMap(rdMap(0), List((N0,N0))) && emptyMap(rdMap(1)))
      // No secondaries
      assert(testHooks.getSecondaryInfo(map1).isEmpty)
    } // end of for loop

    // Secondary induced transitions
    assert(testHooks.acquiredRefs.isEmpty)

    // Overall result
    val (result,result1) = sreou()
    assert(result.length == 1 && result1.isEmpty && {
      val states = applyRemapping(result(0)._1, cv.components)
      /*result(0)._2*/states.sameElements(Array(bNode(N3,N4), cNode(N4,Null)))
    })
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
    val sreou = new SingleRefEffectOnUnification(mkTrans(pre, post), cv)
    val testHooks = sreou.TestHooks

    for((map1,unifs) <- allUnifs){
      if(unifs.isEmpty){                                   // no unification
        val (otherArgs, oaBitMap) = testHooks.mkOtherArgs(map1, unifs)
        // Just N4, from post.servers
        assert(otherArgs(0) == List(N4) && otherArgs(1).isEmpty)
        assert(checkMap(map1(0), List((N0,N0))) && emptyMap(map1(1)))
        val rdMaps = testHooks.extendToRDMap(map1,oaBitMap)
        // Map any of (N1, N2, N3, none) to N4
        assert(rdMaps.length == 4 &&
          rdMaps.forall(map2 => (
            checkMap(map2(0), List((N0,N0))) || 
              List(N1,N2,N3).exists(n => 
                checkMap(map2(0), List((N0,N0), (n,N4))))
          ) && emptyMap(map2(1))))

        // Secondary info; link from the Nd_C
        val secondaryInfo = testHooks.getSecondaryInfo(map1)
        assert(secondaryInfo.length == 1); val (map2,i) = secondaryInfo(0)
        assert(i == 1 && checkMap(map2(0), List((N0,N0), (N1,N2))) && 
          emptyMap(map2(1)))
        val sc = post.components(i)
        val (otherArgs1, oaBitMap1) = testHooks.mkSecondaryOtherArgsMap(map2, sc)
        // N4 from post.fixed; N1 from sc
        assert(otherArgs1(0).sorted == List(N1,N4) && otherArgs1(1).isEmpty)
      } // end of no unifications case

      else{                                            // unify the Nd_A's
        val map1List = List((N0,N0), (N1,N1), (N2,N3))
        assert(unifs == List((0,1)) && checkMap(map1(0), map1List) && 
          emptyMap(map1(1)) )
        val (otherArgs, oaBitMap) = testHooks.mkOtherArgs(map1, unifs)
        // N4 from post.servers; N2 from the post-state of the unified component
        assert(otherArgs(0).sorted == List(N2,N4) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,oaBitMap)
        // Can map N3 to (N2, N4 or none)
        assert(rdMaps.length == 3 &&
          rdMaps.forall(map2 =>
            List(N2,N4,-1).exists(n => checkMap(map2(0), (N3,n)::map1List)) &&
              emptyMap(map2(1)) ))
        // No secondaries: prevented by unification
        assert(testHooks.getSecondaryInfo(map1).isEmpty)
      } // end of unifying Nd_A's case
    } // end of for(... <- allUnifs)

    // Secondary induced transitions
    val acqRefs: Array[(Int,Parameter)] = testHooks.acquiredRefs
    assert(acqRefs.sameElements(Array((1,(0,N2)))), acqRefs.mkString(", "))

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
      assert(result.exists(tuple => {
        val states = applyRemapping(tuple._1, cv.components)
        exp.sameElements(states/*tuple._2*/)
      }))
    // Expected from result1
    val expected1 = List(
      Array(aNode(N2,N4), bNode(N4,N5)), Array(aNode(N2,N5), bNode(N5,N6))
    )
    assert(result1.length == expected1.length)
    for(exp <- expected1) 
      assert(result1.exists(tuple => {
        val states = applyRemapping(tuple._1, cv.components)
        exp.sameElements(states /*tuple._1*/)
      }))
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
    val cv = new ComponentView(servers3(N0), aNode(N1, N2), Array(bNode(N2, N3)))
    val allUnifs = mkUnifs(pre, cv); assert(allUnifs.length == 3)
    val sreou = new SingleRefEffectOnUnification(mkTrans(pre, post), cv)
    val testHooks = sreou.TestHooks

    for((map1,unifs) <- allUnifs){
      if(unifs.isEmpty){
        val map1List = List((N0,N0))
        assert(checkMap(map1(0), map1List) && emptyMap(map1(1)))
        val (otherArgs, oaBitMap) = testHooks.mkOtherArgs(map1, unifs)
        // Just N5, from post.servers
        assert(otherArgs(0) == List(N5) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,oaBitMap)
        // Map any of (N1,N2,N3,none) to N5
        assert(rdMaps.length == 4 &&
          rdMaps.forall(map2 => (
            checkMap(map2(0), map1List) ||
              List(N1,N2,N3).exists(n => checkMap(map2(0), (n,N5)::map1List))
          ) && emptyMap(map2(1)) ))
      }
      else if(unifs == List((0,1))){ // unify the Nd_A's
        val map1List = List((N0,N0), (N1,N1), (N2,N3))
        assert(checkMap(map1(0), map1List) && emptyMap(map1(1)))
        val (otherArgs, oaBitMap) = testHooks.mkOtherArgs(map1, unifs)
        // N5 from post.servers; N2 from the post-state of the Nd_A; N4 from
        // the post-state of the Nd_B (acquired reference).
        assert(otherArgs(0).sorted == List(N2,N4,N5) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,oaBitMap)
        // Map N3 to any of (N2,N4,N5,none)
        assert(rdMaps.length == 4 &&
          rdMaps.forall(map2 => emptyMap(map2(1)) && 
            List(N2,N4,N5,-1).exists(n => checkMap(map2(0), (N3,n)::map1List))))
      }
      else{ // unify the Nd_B's
        val map1List = List((N0,N0), (N2,N2), (N3,N4))
        assert(unifs == List((1,2)) && checkMap(map1(0), map1List) && 
          emptyMap(map1(1)))
        val (otherArgs, oaBitMap) = testHooks.mkOtherArgs(map1, unifs)
        // Just N5 from post.servers
        assert(otherArgs(0) == List(N5) && otherArgs(1).isEmpty)
        val rdMaps = testHooks.extendToRDMap(map1,oaBitMap)
        // Map N1 to N5 or nothing
        assert(rdMaps.length == 2 && 
          rdMaps.forall(map2 => emptyMap(map2(1)) &&
            List(N5,-1).exists(n => checkMap(map2(0), (N1,n)::map1List))))
      } // end of unifying Nd_B's case
      // No secondary transitions, since mapping N1 to N2 requires unifying
      // Nd_A(N1) with Nd_B(N_2)
      assert(testHooks.getSecondaryInfo(map1).isEmpty)
    } // end of outer for loop

    // Secondary induced transitions; but not achievable
    assert(testHooks.acquiredRefs.sameElements(Array((1,(0,N2)))))

    // Check top-level result
    val (result,result1) = sreou()
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
      assert(result.exists(tuple => {
        val states = applyRemapping(tuple._1, cv.components)
        exp.sameElements(states/*tuple._2*/)
      }))
    assert(result1.isEmpty)
  }

  /** Main function. */
  def apply() = {
    singleRef = true
    println("===SingleRefEffectOnUnificationTest===")
    test1; test2; test3; test4; test5
    singleRef = false
  }
}
