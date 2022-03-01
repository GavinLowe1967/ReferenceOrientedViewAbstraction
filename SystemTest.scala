package ViewAbstraction.SystemP

import ViewAbstraction._

/** Unit tests for System.scala.  These assume that test3.csp is loaded. */
object SystemTest{
  // import SystemP.System._
  import TestStates._
  // import View.showStates

  private def consistentStatesTest(system: System) = {
    def test1 = {
      // println("test1")
      val conc = 
        new Concretization(servers1, Array(aNode(N0,N1), aNode(N1,Null)))
      val cv1 = new ComponentView(servers1, pushSt(T0,N0), Array(aNode(N0,N1)))
      val buff = system.consistentStates(conc, (0,N2), -1, cv1)
      // node of cv1 gets renamed to aNode(N2,N0|N1|N3)
      // println(buff.mkString("\n"))
      assert(buff.length == 3 && buff.forall{case(n,nexts) =>
        (n == aNode(N2,N0) || n == aNode(N2,N1) || n == aNode(N2,N3)) &&
        nexts.sameElements(Array(n)) // == List(n)
      })
    }
    def test2 = {
      // println("test2")
      val conc = 
        new Concretization(servers1, Array(aNode(N0,N1), aNode(N1,Null)))
      val cv1 = new ComponentView(servers1, pushSt(T0,N0), Array(aNode(N0,N1)))
      val buff = system.consistentStates(conc, (0,N1), -1, cv1)
      // Any renaming of aNode(N0,N1) to N1 would be inconsistent with
      // aNode(N1,Null) in conc.
      assert(buff.isEmpty)
    }    
    def test3 = {
      // println("test3")
      val conc = 
        new Concretization(servers1, Array(pushSt(T0,N0), aNode(N0,N1)))
      val cv1 = new ComponentView(servers1, aNode(N0,N1), Array(aNode(N1,N2)))
      val buff = system.consistentStates(conc, (0,N2), -1, cv1)
      // Either node of cv1 can be renamed to aNode(N2,N0|N1|N3)
      // println(buff.map{ case (n,nexts) => 
      //   n.toString+", "+nexts.mkString("(",",",")") }.mkString("\n"))
      assert(buff.length == 3 && buff.forall{case(n,nexts) =>
        (n == aNode(N2,N0) || n == aNode(N2,N1) || n == aNode(N2,N3)) &&
        nexts.sameElements(Array(n)) // == List(n)
      })
    }
    def test4 = {
      // println("test4")
      val conc = 
        new Concretization(servers2, Array(aNode(N0,N1), aNode(N1,Null)))
      val cv1 = new ComponentView(servers2, pushSt(T0,N0), Array(aNode(N0,N1)))
      val buff = system.consistentStates(conc, (0,N2), -1, cv1)
      // Now N0 can't be renamed, because it's in servers2
      assert(buff.isEmpty)
    }
    def test5 = {
      // println("test5")
      val conc = 
        new Concretization(servers1, Array(aNode(N0,N1), bNode(N1,Null)))
      val cv1 = new ComponentView(servers1, aNode(N0,N1), Array(bNode(N1,N2)))
      // N0 of cv1 can't be renamed to N0 because they point to inconsistent
      // nodes.  N1 of cv1 can't be renamed to N0 because they have different
      // control states.
      val buff1 = system.consistentStates(conc, (0,N0), -1, cv1)
      assert(buff1.isEmpty)
      // Neither node of cv1 can be renamed to N1
      val buff2 = system.consistentStates(conc, (0,N1), -1, cv1)
      assert(buff2.isEmpty)
      // N0 can be renamed to N2, pointing to a node distinct from N0,N1,N2.
      // N1 can be renamed to N2, pointing to N0, N1 or a distinct node.
      val buff3 = system.consistentStates(conc, (0,N2), -1, cv1)
      assert(buff3.length == 4 && buff3.forall{case(n,nexts) =>
        (n == aNode(N2,N3) || 
          n == bNode(N2,N0) || n == bNode(N2,N1) || n == bNode(N2,N3)) &&
        nexts.sameElements(Array(n)) // == List(n)
      })
      // println(buff3.mkString("\n"))
    }
    // Now tests on singletons
    def test6 = {
      // println("test6")
      val conc = 
        new Concretization(servers1, Array(aNode(N0,N1), aNode(N1,Null)))
      val cv1 = new ComponentView(servers1, aNode(N0,Null), Array())
      // N0 can be renamed to N2
      val buff1 = system.consistentStates(conc, (0,N2), -1, cv1)
      assert(buff1.length == 1 && buff1.forall{case(n,nexts) =>
        n == aNode(N2,Null) && nexts.toList == List(n)
      })
      // N0 can be renamed to N1
      val buff2 = system.consistentStates(conc, (0,N1), -1, cv1)
      assert(buff2.length == 1 && buff2.forall{case(n,nexts) =>
        n == aNode(N1,Null) && nexts.toList == List(n)
      })
      // N0 can't be renamed to N0 (fails to match)
      val buff3 = system.consistentStates(conc, (0,N0), -1, cv1)
      assert(buff3.isEmpty)
      // println(buff3.mkString("\n"))
    }
    def test7 = {
      val conc = 
        new Concretization(servers2, Array(aNode(N0,N1), aNode(N1,Null)))
      val cv1 = new ComponentView(servers2, aNode(N1,Null), Array())
      // N1 can be renamed to N2
      val buff1 = system.consistentStates(conc, (0,N2), -1, cv1)
      assert(buff1.length == 1 && buff1.forall{case(n,nexts) =>
        n == aNode(N2,Null) && nexts.toList == List(n)
      })
      // N1 can be renamed to N1
      val buff2 = system.consistentStates(conc, (0,N1), -1, cv1)
      assert(buff2.length == 1 && buff2.forall{case(n,nexts) =>
        n == aNode(N1,Null) && nexts.toList == List(n)
      })
      // N1 can't be renamed to N0
      val buff3 = system.consistentStates(conc, (0,N0), -1, cv1)
      assert(buff3.isEmpty)
    }
    def test8 = {
      // println("test8")
      val conc = 
        new Concretization(servers2, Array(aNode(N0,Null)))
      val cv1 = new ComponentView(servers2, aNode(N1,Null), Array())
      // N1 can be renamed to N2
      val buff1 = system.consistentStates(conc, (0,N2), -1, cv1)
      assert(buff1.length == 1 && buff1.forall{case(n,nexts) =>
        n == aNode(N2,Null) && nexts.toList == List(n)
      })
      // N1 cannot be renamed to N0 because of the servers
      val buff2 = system.consistentStates(conc, (0,N0), -1, cv1)
      assert(buff2.isEmpty)
    }
    // Node about to be initiailised
    def test9 = {
      println("test9")
      val conc = 
        new Concretization(servers2, Array(initNodeSt(T0,N0), aNode(N0,N1)))
      val cv1 = new ComponentView(servers2, initNode(N1), Array())
      val e = system.fdrSession.eventToInt("initNode.T0.N2.A.N0")
      val buff = system.consistentStates(conc, (0,N2), e, cv1)
      // println("buff = "+buff.mkString("\n")+"XXX")
      println(buff.map{ case (n,nexts) => 
        n.toString+", "+nexts.mkString("(",",",")") }.mkString("\n"))
      assert(buff.length == 1 && buff(0)._1 == initNode(N2) && 
        buff(0)._2.toList == List(aNode(N2,N0)))
    }

    test1; test2; test3; test4; test5; test6; test7; test8; test9
  }

// IMPROVE: add some transitions to above

  /** Test system, assumed to correspond to test3.scala. */
  def test(system: System) = {
    println("SystemTest")
    consistentStatesTest(system)
  }

}
  
