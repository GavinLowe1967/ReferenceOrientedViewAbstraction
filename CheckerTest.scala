package ViewAbstraction

import scala.collection.mutable.ArrayBuffer

class CheckerTest(system: SystemP.System) extends Checker(system){
  import TestStates._

  val (sav, initViews) = system.initViews; sysAbsViews = sav
  nextNewViews = new ArrayBuffer[View]

  /** Test of effectOn. */
  private def effectOnTest = {
    // transition on getLock.T0
    def test1 = {
      val pre = new Concretization(servers0, Array(initSt(T0)))
      val post = new Concretization(servers1, Array(gotLock(T0)))
      // servers should evolve to servers1 on following two
      effectOn(pre, post, new ComponentView(servers0, initNode(N0), Array()))
      effectOn(pre, post, new ComponentView(servers0, aNode(N1, Null), Array()))
      // On following: servers could evolve to servers1 with a different
      // thread; or this could match the transition.
      effectOn(pre, post, new ComponentView(servers0, initSt(T0), Array()))
      assert(nextNewViews.length == 4 &&
        nextNewViews(0) == new ComponentView(servers1, initNode(N0), Array()) &&
        nextNewViews(1) == new ComponentView(servers1, aNode(N0, Null), Array()) &&
        nextNewViews.contains(new ComponentView(servers1, initSt(T1), Array())) &&
        nextNewViews.contains(new ComponentView(servers1, gotLock(T0), Array()))
      )
    }
    // transition on setTop.T0.N1
    def test2 = {
      println("test2")
      nextNewViews = new ArrayBuffer[View]
      val serversA = ServerStates(List(lock1(T0), top(N0), wd0B))
      val pre = new Concretization(serversA, Array(setTopB(T0, N1), bNode(N1,N0)))
      val serversB = ServerStates(List(lock1(T0), top(N1), wd1))
      val post = new Concretization(serversB, Array(unlock(T0)))
      val serversB1 = ServerStates(List(lock1(T0), top(N0), wd1))
      // On following: servers evolves to serversB1 and aNode renamed to N1.
      effectOn(pre, post, new ComponentView(serversA, aNode(N0, Null), Array()))
      assert(nextNewViews(0) ==
        new ComponentView(serversB1, aNode(N1, Null), Array()))
      // On following two: servers evolves to serversB1, nodes renamed
      // N0,N1 -> N1,N2
      effectOn(pre, post, 
        new ComponentView(serversA, aNode(N0,N1), Array(bNode(N1,Null))))
      assert(nextNewViews(1) == 
        new ComponentView(serversB1, aNode(N1,N2), Array(bNode(N2,Null))))
      effectOn(pre, post, 
        new ComponentView(serversA, bNode(N0,N1), Array(bNode(N1,Null))))
      assert(nextNewViews(2) == 
        new ComponentView(serversB1, bNode(N1,N2), Array(bNode(N2,Null))))
      // Following isn't actually a reachable state; evolves as previous.
      effectOn(pre, post,
        new ComponentView(serversA, pushSt(T1,N0), Array(bNode(N0,Null))))
      assert(nextNewViews(3) == 
        new ComponentView(serversB1, pushSt(T1,N1), Array(bNode(N1,Null))))
      assert(nextNewViews.length == 4)
      // Following should have no effect: not unifiable with pre
      effectOn(pre, post,
        new ComponentView(serversA, pushSt(T0,N1), Array(bNode(N1,Null))))
      effectOn(pre, post,
        new ComponentView(serversA, setTopB(T0,N1), Array(bNode(N1,N2))))
      // println; println(nextNewViews.mkString("[", "\n", "]"))
      assert(nextNewViews.length == 4)
    }

    test1; test2
  }

  private def isExtendableTest = {
    isExtendable(???, ???)
  }


  def test = {
    println("CheckerTest")
    effectOnTest
  }

}
