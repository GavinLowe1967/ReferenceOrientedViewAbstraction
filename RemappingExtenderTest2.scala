package ViewAbstraction
import RemapperP._

object RemappingExtenderTest2{

  import TestStates._
  import TestUtils._

  import RemappingExtender.TestHooks1.extendMapToCandidates


  private def test1 = {
    println("=test1=")
    val rdMap: RemappingMap = Array(Array(N0,-1,-1), Array(-1))
    val candidates = Array(
      Array(null, List(N1,N2), List(N1,N3)), Array(List(T0))
    )
    val preParamSizes = Array(4,2); val paramsBound = Array(3,1)
    val maps = 
      extendMapToCandidates(rdMap, candidates, preParamSizes, paramsBound)
    // (3*3-1)*2 combinations; the "-1" is because can't map both N1 and N2 to N1
    assert(maps.length == 16)
    //for(map <- maps) println(Remapper.show(map))
  }

  private def test2 = {
    println("=test2=")
    val rdMap: RemappingMap = Array(Array(N0,-1,-1), Array(-1))
    val candidates = Array(
      Array(null, List(N1,N2), List(N1,N3)), Array(List(T0))
    )
    val preParamSizes = Array(4,2); val paramsBound = Array(2,1)
    val maps = 
      extendMapToCandidates(rdMap, candidates, preParamSizes, paramsBound)
    // 3*1*2 combinations
    assert(maps.length == 6)
    // for(map <- maps) println(Remapper.show(map))
  }

  /* ------------- Tests on extendToMissingComponent. ------------*/

  private def test3 = {
    println("=test3=")
    val map: RemappingMap = Array(Array(N0,-1,-1), Array(-1,-1))
    val c = aNode(N1, N3)
    val extMaps = RemappingExtender.extendToMissingComponent(map, c)
    // for(map <- extMaps) println(Remapper.show(map))
    // Each of N1,N2 can map to N1, N3 or fresh: 3*3-2 (-2 for noninjective)
    assert(extMaps.length == 7)
    for(map1 <- extMaps)
      assert(map1(0)(0) == N0 && map1(1)(0) == T0 && map1(1)(1) == T1 &&
        List(1,2).forall(i =>
          map1(0)(i) == N1 || map1(0)(i) == N3 || map1(0)(i) > 3) &&
        map1(0)(1) != map1(0)(2)
      )
  }

  private def test4 = {
    println("=test4=")
    val map: RemappingMap = Array(Array(N0,-1,-1), Array(-1,-1))
    val c = aNode(N0, N3)
    val extMaps = RemappingExtender.extendToMissingComponent(map, c)
    // for(map <- extMaps) println(Remapper.show(map))
    // Each of N1,N2 can map to N3 or fresh: 2*2-1 (-1 for noninjective)
    assert(extMaps.length == 3)
    for(map1 <- extMaps)
      assert(map1(0)(0) == N0 && map1(1)(0) == T0 && map1(1)(1) == T1 &&
        List(1,2).forall(i => map1(0)(i) == N3 || map1(0)(i) > 3) &&
        map1(0)(1) != map1(0)(2)
      )
  }

  private def test5 = {
    println("=test5=")
    val map: RemappingMap = Array(Array(N0,-1,-1), Array(T0,-1))
    val c = popSt(T1, N0, N3)
    val extMaps = RemappingExtender.extendToMissingComponent(map, c)
    // for(map <- extMaps) println(Remapper.show(map))
    // Each of N1,N2 can map to N3 or fresh: 2*2-1=3 (-1 for noninjective);
    // T1 can map to T1 or fresh
    assert(extMaps.length == 6)
    for(map1 <- extMaps)
      assert(map1(0)(0) == N0 && map1(1)(0) == T0 && 
        (map1(1)(1) == T1 || map1(1)(1) == T2) &&
        List(1,2).forall(i => map1(0)(i) == N3 || map1(0)(i) > 3) &&
        map1(0)(1) != map1(0)(2)
      )
  }

  /** Main function. */
  def apply() = {
    singleRef = true // ; useNewEffectOnStore = false
    println("===RemappingExtenderTest2===")
    test1; test2; 
    test3; test4; test5
  }
}
