package ViewAbstraction

/** A definition of various States, Views, etc., for use in tests. */
object TestStates{
  // Create some states
  // The lock, not held and held
  val lock0 = MyStateMap(-1, 20, Array()) // [20[-1]()
  val lock1 = MyStateMap(-1, 21, Array(0)) // [21[-1](T0)
  
  // Top, pointing to Null and N0
  val TopCS = 22
  val top0 = MyStateMap(-1, TopCS, Array(-1)) // 22[-1](Null)
  val top1 = MyStateMap(-1, TopCS, Array(0)) // 22[-1](N0)
  
  // The watchdog
  val wd0 = MyStateMap(-1, 23, Array()) // 23[-1]() = WD0

  // Nodes
  val initNode0 = MyStateMap(0, 6, Array(0)) // 6[0](N0)
  val initNode1 = MyStateMap(0, 6, Array(1)) // 6[0](N1)
  val aNode0 = MyStateMap(0, 7, Array(0,-1)) // 7[0](N0,Null); (7 = A)
  val aNode1 = MyStateMap(0, 7, Array(0,1)) // 7[0](N0,N1)
  val aNode2 = MyStateMap(0, 7, Array(1,-1)) // 7[0](N1,Null)
  val aNode3 = MyStateMap(0, 7, Array(1,0)) // 7[0](N1,N0)
  val aNode4 = MyStateMap(0, 7, Array(1,2)) // 7[0](N1,N2)
  val aNode5 = MyStateMap(0, 7, Array(2,3)) // 7[0](N2,N3)

  // Threads
  val initSt = MyStateMap(1, 10, Array(0)) // 10[1](T0) = Thread(T0)
  val pushSt = MyStateMap(1, 12, Array(0, 0)) // 12[1](T0,N0) = push... ->

  // Combined servers
  // 21[-1](T0) || 22[-1](Null) || 23[-1]()
  val servers1 = new ServerStates(List(lock1, top0, wd0))
  // 21[-1](T0) || 22[-1](N0) || 23[-1]()
  val servers2 = new ServerStates(List(lock1, top1, wd0))

  // Combined components
  val components1 = Array(pushSt, aNode1) // 12[1](T0,N0) || 7[0](N0,N1)
  // println(servers1.toString+" || "+components1.mkString("[", "||", "]"))
  val nodes = Array(aNode1, aNode4) //  7[0](N0,N1) || 7[0](N1,N2)



}
