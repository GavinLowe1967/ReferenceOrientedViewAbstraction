package ViewAbstraction.SystemP

import ViewAbstraction._

/** Unit tests for System.scala.  These assume that test3.csp is loaded. */
object SystemTest{
  // import SystemP.System._
  import TestStates._
  import View.showStates

  private def consistentStatesTest(system: System) = {
    def test1 = {
      println("test1")
      val conc = 
        new Concretization(servers1, Array(aNode(N0,N1), aNode(N1,Null)))
      val cv1 = new ComponentView(servers1, pushSt(T0,N0), Array(aNode(N0,N1)))
      val buff = system.consistentStates((0,N2), conc, None, cv1)
      // node of cv1 gets renamed to aNode(N2,N0|N1|N3)
      assert(buff.length == 3 && buff.forall{case(n,nexts) =>
        (n == aNode(N2,N0) || n == aNode(N2,N1) || n == aNode(N2,N3)) &&
        nexts == List(n)
      })
    }
    def test2 = {
      println("test2")
      val conc = 
        new Concretization(servers1, Array(aNode(N0,N1), aNode(N1,Null)))
      val cv1 = new ComponentView(servers1, pushSt(T0,N0), Array(aNode(N0,N1)))
      val buff = system.consistentStates((0,N1), conc, None, cv1)
      // Any renaming of aNode(N0,N1) to N1 would be inconsistent with
      // aNode(N1,Null) in conc.
      assert(buff.isEmpty)
    }    
    def test3 = {
      println("test3")
      val conc = 
        new Concretization(servers1, Array(pushSt(T0,N0), aNode(N0,N1)))
      val cv1 = new ComponentView(servers1, aNode(N0,N1), Array(aNode(N1,N2)))
      val buff = system.consistentStates((0,N2), conc, None, cv1)
      // Either node of cv1 can be renamed to aNode(N2,N0|N1|N3)
      assert(buff.length == 3 && buff.forall{case(n,nexts) =>
        (n == aNode(N2,N0) || n == aNode(N2,N1) || n == aNode(N2,N3)) &&
        nexts == List(n)
      })
    }
    def test4 = {
      println("test4")
      val conc = 
        new Concretization(servers2, Array(aNode(N0,N1), aNode(N1,Null)))
      val cv1 = new ComponentView(servers2, pushSt(T0,N0), Array(aNode(N0,N1)))
      val buff = system.consistentStates((0,N2), conc, None, cv1)
      // Now N0 can't be renamed, because it's in servers2
      assert(buff.isEmpty)
    }
    def test5 = {
      println("test5")
      val conc = 
        new Concretization(servers1, Array(aNode(N0,N1), bNode(N1,Null)))
      val cv1 = new ComponentView(servers1, aNode(N0,N1), Array(bNode(N1,N2)))
      // N0 of cv1 can't be renamed to N0 because they point to inconsistent
      // nodes.  N1 of cv1 can't be renamed to N0 because they have different
      // control states.
      val buff1 = system.consistentStates((0,N0), conc, None, cv1)
      assert(buff1.isEmpty)
      // Neither node of cv1 can be renamed to N1
      println("case 2")
      val buff2 = system.consistentStates((0,N1), conc, None, cv1)
      assert(buff2.isEmpty)
      // N0 can be renamed to N2, pointing to a node distinct from N0,N1,N2.
      // N1 can be renamed to N2, pointing to N0, N1 or a distinct node.
      println("case 3")
      val buff3 = system.consistentStates((0,N2), conc, None, cv1)
      assert(buff3.length == 4 && buff3.forall{case(n,nexts) =>
        (n == aNode(N2,N3) || 
          n == bNode(N2,N0) || n == bNode(N2,N1) || n == bNode(N2,N3)) &&
        nexts == List(n)
      })
      println(buff3.mkString("\n"))
    }

    test1; test2; test3; test4; test5
  }

  /** Test system, assumed to correspond to test3.scala. */
  def test(system: System) = {
    println("SystemTest")
    consistentStatesTest(system)
  }

}
  
