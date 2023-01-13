package ViewAbstraction

/** Various helper functions for tests. */
object TestUtils{

  // ======== Helper functions

  /** Check that map is the mapping {i -> j}. */
  def checkMap(map: Array[Int], i: Int, j: Int) =
    map(i) == j && map.indices.forall(i1 => i1 == i || map(i1) == -1)

  /** Check that map is the mapping {(i,j) | (i,j) <- pairs}. */
  def checkMap(map: Array[Int], pairs: List[(Int,Int)]) =
    map.indices.forall(i => pairs.filter(_._1 == i) match{
      case List() => map(i) == -1
      case List((i1,j)) => map(i) == j
      case _ => ??? // Shouldn't happen
    })

  def emptyMap(map: Array[Int]) = map.forall(_ == -1)
}
