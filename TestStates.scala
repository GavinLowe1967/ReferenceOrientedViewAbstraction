package ViewAbstraction

/** A definition of various States, Views, etc., for use in tests.  These are
  * consistent with the file test-file.csp. */
object TestStates{
  /** Print out all the states.  Normally not called, but useful if the
    * underlying file test-file.csp is changed. */
  def report = {
    // Map showing expected number of arguments for each control state.
    val csMap = new scala.collection.mutable.HashMap[Int,Int] 
    val states = MyStateMap.toArray
    for(i <- 0 until states.length){
      val st = states(i)
      csMap.get(st.cs) match{
        case Some(n) =>
          assert(st.length == n, s"Found state $st; expected length $n")
        case None => csMap.put(st.cs, st.length);  println(st.toString0)
      }
    }
  }

  // Create some states
  // The lock, not held and held
  val lock0 = MyStateMap(-1, 30, Array()) // [20[-1]()
  def lock1(t: Int) = MyStateMap(-1, 31, Array(t)) // [21[-1](T0)
  
  // Top, pointing to n
  def top(n: Int) = MyStateMap(-1, 32, Array(n)) // +3
  
  // The watchdog
  val wd0 = MyStateMap(-1, 33, Array()) //  WD0
  val wd0B = MyStateMap(-1, 35, Array()) // push2!B -> WD1
  val wd1 = MyStateMap(-1, 37, Array()) // WD1

  // Nodes
  val N0 = 0; val N1 = 1; val N2 = 2; val N3 = 3; val N4 = 4; val N5 = 5
  val N6 = 6; val N7 = 7
  val Null = -1
  def initNode(n: Int) = MyStateMap(0, 6, Array(n))
  val initNode1 = MyStateMap(0, 6, Array(N1))
  def aNode(id: Int, nxt: Int) = MyStateMap(0, 7, Array(id,nxt))
  def bNode(id: Int, nxt: Int) = MyStateMap(0, 8, Array(id,nxt))
  def cNode(id: Int, nxt: Int) = MyStateMap(0, 9, Array(id,nxt))

  // Node with two references
  def dNode(id: Int, nxt: Int, prev: Int) = MyStateMap(0, 10, Array(id,nxt,prev))

  // Threads
  val T0 = 0; val T1 = 1; val T2 = 2; val T3 = 3
  // Initial state of Thread(t)
  def initSt(t: Int) = MyStateMap(1, 13, Array(t))
  // Thread with lock, doing push; getTop.me?top -> ...
  def gotLock(t: Int) = MyStateMap(1, 14, Array(t))
  // Thread with two refs to node, doing a pop, I think
  def popSt(t: Int, n1: Int, n2: Int) = MyStateMap(1, 18, Array(t,n1,n2))
  //  push.me?v -> ...
  def pushSt(t: Int, n: Int) = MyStateMap(1, 23, Array(t,n))
  // State of thread t about to do initNode.t?node!A.n -> ...
  def initNodeSt(t: Int, n: Int) = MyStateMap(1, 26, Array(t,n))
  // State of thread about to do a setTop.t.n.PushOp.B
  def setTopB(t: Int, n: Int) = MyStateMap(1, 28, Array(t,n))
  // Unlock(t)
  def unlock(t: Int) = MyStateMap(1, 22, Array(t))
  // Popping thread: getDatum.t.n1?d -> setTop.t.n2.PopOp.d -> ...
  def getDatumSt(t: Int, n1: Int, n2: Int) = MyStateMap(1, 18, Array(t,n1,n2))

  // Combined servers
  val servers0 = ServerStates(List(lock0, top(Null), wd0))
  val servers1 = ServerStates(List(lock1(T0), top(Null), wd0))
  val servers2 = ServerStates(List(lock1(T0), top(N0), wd0))

  // Combined components
  val components1 = Array(pushSt(T0,N0), aNode(0,1))
  val nodes = Array(aNode(0,1), aNode(1,2))



}
