package ViewAbstraction

/** A definition of various States, Views, etc., for use in tests.  These are
  * consistent with the file test3.csp. */
object TestStates{
  // Create some states
  // The lock, not held and held
  val lock0 = MyStateMap(-1, 20, Array()) // [20[-1]()
  def lock1(t: Int) = MyStateMap(-1, 21, Array(t)) // [21[-1](T0)
  
  // Top, pointing to Null and N0
  val TopCS = 22
  // val top0 = MyStateMap(-1, TopCS, Array(-1)) // 22[-1](Null)
  // val top1 = MyStateMap(-1, TopCS, Array(0)) // 22[-1](N0)
  def top(n: Int) = MyStateMap(-1, TopCS, Array(n))
  
  // The watchdog
  val wd0 = MyStateMap(-1, 23, Array()) // 23[-1]() = WD0

  // Nodes
  val N0 = 0; val N1 = 1; val N2 = 2; val N3 = 3; val N4 = 4; val Null = -1
  val initNode0 = MyStateMap(0, 6, Array(N0)) // 6[0](N0)
  val initNode1 = MyStateMap(0, 6, Array(N1)) // 6[0](N1)
  def aNode(id: Int, nxt: Int) = MyStateMap(0, 7, Array(id,nxt))
  def bNode(id: Int, nxt: Int) = MyStateMap(0, 8, Array(id,nxt))
  //val aNode0 = MyStateMap(0, 7, Array(0,-1)) // 7[0](N0,Null); (7 = A)
  // val aNode1 = MyStateMap(0, 7, Array(0,1)) // 7[0](N0,N1)
  //val aNode2 = MyStateMap(0, 7, Array(1,-1)) // 7[0](N1,Null)
  // val aNode3 = MyStateMap(0, 7, Array(1,0)) // 7[0](N1,N0)
  // val aNode4 = MyStateMap(0, 7, Array(1,2)) // 7[0](N1,N2)
  // val aNode5 = MyStateMap(0, 7, Array(2,3)) // 7[0](N2,N3)
  // val aNodeN2Null = MyStateMap(0, 7, Array(2,-1)) // 7[0](N2,Null)

  // Threads
  val T0 = 0; val T1 = 1; val T2 = 2; val T3 = 3
  val initSt = MyStateMap(1, 10, Array(T0)) // 10[1](T0) = Thread(T0)
  // val pushSt = MyStateMap(1, 12, Array(T0, N0)) // 12[1](T0,N0) = push... ->
  def pushSt(t: Int, n: Int) = MyStateMap(1, 12, Array(t,n))

  // Combined servers
  // 21[-1](T0) || 22[-1](Null) || 23[-1]()
  val servers1 = new ServerStates(List(lock1(T0), top(Null), wd0))
  // 21[-1](T0) || 22[-1](N0) || 23[-1]()
  val servers2 = new ServerStates(List(lock1(T0), top(N0), wd0))

  // Combined components
  val components1 = Array(pushSt(T0,N0), aNode(0,1))
  // 12[1](T0,N0) || 7[0](N0,N1)
  // println(servers1.toString+" || "+components1.mkString("[", "||", "]"))
  val nodes = Array(aNode(0,1), aNode(1,2)) //  7[0](N0,N1) || 7[0](N1,N2)



}
