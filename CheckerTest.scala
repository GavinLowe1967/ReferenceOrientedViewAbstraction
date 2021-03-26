package ViewAbstraction

import scala.collection.mutable.{ArrayBuffer,HashSet}

class CheckerTest(system: SystemP.System) extends Checker(system){
  import TestStates._

  def reset() = { 
    val (sav, initViews) = system.initViews; sysAbsViews = sav
    nextNewViews = new HashSet[ComponentView] 
  }

  reset()

  /** Test of effectOn. */
  private def effectOnTest = {
    def mkCV(servers: ServerStates, princ: State, others: Array[State]) = {
      val cv = new ComponentView(servers, princ, others); cv.ply = 0; cv
    }

    println("== effectOnTest ==")
    // transition on getLock.T0
    def test1 = {
      val pre = new Concretization(servers0, Array(initSt(T0)))
      val post = new Concretization(servers1, Array(gotLock(T0)))
      pre.ply = 0; post.ply = 0
      // servers should evolve to servers1 on following two
      ply = 2
      effectOn(pre, 1, post, mkCV(servers0, initNode(N0), Array()))
      effectOn(pre, 1, post, mkCV(servers0, aNode(N1, Null), Array()))
      // println(nextNewViews.mkString("\n"))
      assert(nextNewViews.size == 2)
      assert(nextNewViews(new ComponentView(servers1, initNode(N0), Array())))
      assert(nextNewViews(new ComponentView(servers1, aNode(N0, Null), Array())))

      // On following: servers could evolve to servers1 with a different
      // thread
      effectOn(pre, 1, post, mkCV(servers0, initSt(T0), Array()))
      // println("\n"+nextNewViews.mkString("\n"))
      assert(nextNewViews.size == 3)
      assert(nextNewViews(new ComponentView(servers1, initSt(T1), Array())))
      // Following no longer included: it just recreates the transition.
      // assert(nextNewViews(new ComponentView(servers1, gotLock(T0), Array())))
    }

    // transition on setTop.T0.N1
    def test2 = {
      println("= test2 =")
      reset() // nextNewViews = new ArrayBuffer[View]
      val serversA = ServerStates(List(lock1(T0), top(N0), wd0B))
      val pre = new Concretization(serversA, Array(setTopB(T0,N1), bNode(N1,N0)))
      val serversB = ServerStates(List(lock1(T0), top(N1), wd1))
      val post = new Concretization(serversB, Array(unlock(T0), bNode(N1,N0)))
      val serversB1 = ServerStates(List(lock1(T0), top(N0), wd1))
      pre.ply = 0; post.ply = 0

      // On following: servers evolves to serversB1 and aNode renamed to N1.
      effectOn(pre, 1, post, mkCV(serversA, aNode(N0, Null), Array()))
      assert(nextNewViews.size == 1)
      assert(nextNewViews.contains(
        new ComponentView(serversB1, aNode(N1, Null), Array())))

      // On following: servers evolves to serversB1.  The bNode here doesn't
      // unify with that in pre, so Ni gets mapped to a fresh value.
      effectOn(pre, 1, post, 
        mkCV(serversA, aNode(N0,N1), Array(bNode(N1,Null))))
      assert(nextNewViews.size == 2)
      assert(nextNewViews.contains(
        new ComponentView(serversB1, aNode(N1,N2), Array(bNode(N2,Null)))))

      effectOn(pre, 1, post, 
        mkCV(serversA, bNode(N0,N1), Array(bNode(N1,Null))))
      // Servers evolve to serversB1.  Again no unification
      assert(nextNewViews.size == 3)
      assert(nextNewViews.contains(
        new ComponentView(serversB1, bNode(N1,N2), Array(bNode(N2,Null)))))

      // Following isn't actually a reachable state; evolves as previous.
      println("-------")
      effectOn(pre, 1, post,
        mkCV(serversA, pushSt(T1,N0), Array(bNode(N0,Null))))
      assert(nextNewViews.size == 4)
      assert(nextNewViews.contains(
        new ComponentView(serversB1, pushSt(T1,N1), Array(bNode(N1,Null)))))

      // Following should have no effect: not unifiable with pre
      effectOn(pre, 1, post,
        new ComponentView(serversA, pushSt(T0,N1), Array(bNode(N1,Null))))
      effectOn(pre, 1, post,
        new ComponentView(serversA, setTopB(T0,N1), Array(bNode(N1,N2))))
      assert(nextNewViews.size == 4)

      val cv1 = new ComponentView(serversA, pushSt(T1,N1), Array(bNode(N1,N0)))
      cv1.ply = 1
      effectOn(pre, 1, post, cv1)
      // println("\n"+nextNewViews.mkString("\n"))
      // The two bNodes unify
      assert(nextNewViews.contains(
        new ComponentView(serversB1, Array(pushSt(T1,N0), bNode(N0,N1)))))
      // No unification
      assert(nextNewViews.contains(
        new ComponentView(serversB1, Array(pushSt(T1,N1), bNode(N1,N2)))))
      assert(nextNewViews.size == 6)
    }

    // Test with initialisation of node
    def test3 = {
      println("= test3 =\n")
      reset()
      val pre = new Concretization(servers1, 
        Array(initNodeSt(T0,Null), initNode(N0)))
      // servers1 has reference to T0
      val post = new Concretization(servers1,
        Array(setTopB(T0,N0), bNode(N0,Null)))
      pre.ply = 0; post.ply = 0

      val cv1 = new ComponentView(servers1, Array(initNodeSt(T0,Null)))
      cv1.ply = 1
      effectOn(pre, 1, post, cv1)        
      // println("\n"+nextNewViews.mkString("\n"))
      assert(nextNewViews.contains(
        new ComponentView(servers1, Array(setTopB(T0,N0), bNode(N0,Null)))))
      assert(nextNewViews.size == 1)

      val cv2 = new ComponentView(servers1, Array(initNode(N0))); cv2.ply = 1
      effectOn(pre, 1, post, cv2)        
      //println("\n"+nextNewViews.mkString("\n"))
      // With unification
      assert(nextNewViews.contains(
        new ComponentView(servers1, Array(bNode(N0,Null)))))
      // Without unification -- not included
      // assert(nextNewViews.contains(
      //   new ComponentView(servers1, Array(initNode(N0)))))
      assert(nextNewViews.size == 2)

      val cv3 = new ComponentView(servers1, Array(aNode(N0,Null))); cv3.ply = 1
      effectOn(pre, 1, post, cv3)        
      //println("\n"+nextNewViews.mkString("\n"))
      // Without unification -- not included
      // assert(nextNewViews.contains(
      //   new ComponentView(servers1, Array(aNode(N0,Null)))))
      assert(nextNewViews.size == 2)
    }

    test1; test2; test3
  }

  /** Test on compatibleWith. */
  private def compatibleWithTest = {
    println("== compatibleWithTest ==")
    reset()
    def test1 = {
      // Views with servers0 and initSt(T0) or initNode(N0) are in sysAbsViews
      assert(compatibleWith(new Concretization(servers0, Array()), initSt(T0)))
      assert(compatibleWith(new Concretization(servers0, Array()), initSt(T1)))
      assert(compatibleWith(new Concretization(servers0, Array()), initNode(N0)))
      assert(compatibleWith(new Concretization(servers0, Array()), initNode(N1)))
      // But not other views
      assert(!compatibleWith(
        new Concretization(servers0, Array()), pushSt(T0, N0)))
      assert(!compatibleWith(
        new Concretization(servers0, Array()), aNode(N0, Null)))
      // Add another view, and check compatibility
      sysAbsViews.add(new ComponentView(servers0, aNode(N0, Null), Array()))
      assert(compatibleWith(
        new Concretization(servers0, Array()), aNode(N0, Null)))
      assert(compatibleWith(
        new Concretization(servers0, Array()), aNode(N1, Null)))
      assert(!compatibleWith(
        new Concretization(servers0, Array()), aNode(N0, N1)))
      // Add a view where Top has reference to N0.
      sysAbsViews.add(new ComponentView(servers2, aNode(N0, Null), Array()))
      assert(compatibleWith(
        new Concretization(servers2, Array()), aNode(N0, Null)))
      assert(!compatibleWith(
        new Concretization(servers2, Array()), aNode(N1, Null)))
    }

    def test2 = {
      reset()
      // println("= test2= ")
      assert(! compatibleWith(
        new Concretization(servers2, Array(aNode(N0,Null))), aNode(N1,N0)))
      sysAbsViews.add(
        new ComponentView(servers2, aNode(N1,N0), Array(bNode(N0,Null))))
      assert(compatibleWith(
        new Concretization(servers2, Array()), aNode(N1,N0)))
      assert(compatibleWith(
        new Concretization(servers2, Array(bNode(N0,Null))), aNode(N1,N0)))
      // Following should give false: aNode(N0,Null) || aNode(N1,N0) isn't
      // compatible with the view just added, because that has N0 as a bNode.
      assert(! compatibleWith(
        new Concretization(servers2, Array(aNode(N0,Null))), aNode(N1,N0)))
      // Similarly for following
      assert(! compatibleWith(
        new Concretization(servers2, Array(bNode(N0,Null))), bNode(N1,N0)))
      // The following should make aNode(N0,Null) || aNode(N1,N0) compatible
      sysAbsViews.add(
        new ComponentView(servers2, aNode(N1,N0), Array(aNode(N0,Null))))
      assert(compatibleWith(
        new Concretization(servers2, Array(bNode(N0,Null))), aNode(N1,N0)))
      assert( compatibleWith(
        new Concretization(servers2, Array(aNode(N0,Null))), aNode(N1,N0)))
      assert(! compatibleWith(
        new Concretization(servers2, Array(bNode(N0,Null))), bNode(N1,N0)))
      // And the following should make bNode(N0,Null) || bNode(N1,N0) compatible.
      sysAbsViews.add(
        new ComponentView(servers2, bNode(N1,N0), Array(bNode(N0,Null))))
      assert(compatibleWith(
        new Concretization(servers2, Array(bNode(N0,Null))), aNode(N1,N0)))
      assert(compatibleWith(
        new Concretization(servers2, Array(aNode(N0,Null))), aNode(N1,N0)))
      assert(compatibleWith(
        new Concretization(servers2, Array(bNode(N0,Null))), bNode(N1,N0)))
    }

    test1; test2

  }

  /** Test containsReferencingView. */
  private def containsReferencingViewTest = {
    def test1 = {
      reset()
      val conc = 
        new Concretization(servers1, Array(initNodeSt(T0,N0), aNode(N0,N1)))
      val st = initNode(N1)
      assert(findReferencingView(conc, st, 1) == null)
      val cv = new ComponentView(servers1, aNode(N0,N1), Array(st))
      sysAbsViews.add(cv)
      assert(findReferencingView(conc, st, 1) == cv)
    }
    def test2 = {
      reset()
      val conc = 
        new Concretization(servers1, Array(initNodeSt(T0,N0), aNode(N0,N1)))
      val st = bNode(N1,N2)
      assert(findReferencingView(conc, st, 1) == null)
      // Following matches control state of st, but not its next ref
      sysAbsViews.add(
        new ComponentView(servers1, aNode(N0,N1), Array(bNode(N1,Null))) )
      assert(findReferencingView(conc, st, 1) == null)
      // Following should match
      val cv = new ComponentView(servers1, aNode(N0,N1), Array(st))
      sysAbsViews.add(cv)
      assert(findReferencingView(conc, st, 1) == cv)
    }
    def test3 = {
      reset()
      val conc = 
        new Concretization(servers1, Array(initNodeSt(T0,N0), aNode(N0,N1)))
      val st = bNode(N1,N2)
      // Test renaming of the "next" component of st
      val cv = new ComponentView(servers1, aNode(N0,N1), Array(bNode(N1,N3)))
      sysAbsViews.add(cv)
      assert(findReferencingView(conc, st, 1) == cv)
    }
    // Need to find tests where views contain more than two states

    def test4 = { 
      // println("= test4 =")
      reset()
      val conc = new Concretization(servers2, 
        Array(getDatumSt(T0,N0,N1), aNode(N0,N1), bNode(N1,Null), cNode(N2, N1)))
      val st = cNode(N1,Null)
      assert(findReferencingView(conc, st, 3) == null)
      // With following, cNode(N2, N1) gets renamed to cNode(N1,N2), but
      // doesn't include a renaming of st.
      sysAbsViews.add(
        new ComponentView(servers2, cNode(N1,N2), Array(aNode(N2,Null))))
      assert(findReferencingView(conc, st, 3) == null)
      // With following, cNode(N2, N1) gets renamed to cNode(N1,N2), and st
      // gets renamed to cNode(N2,Null).  However, in conc, N2 points to a
      // B-node, so this should fail.
      sysAbsViews.add(
        new ComponentView(servers2, cNode(N1,N2), Array(cNode(N2,Null))))
      assert(findReferencingView(conc, st, 3) == null)
      // With following, cNode(N2, N1) gets renamed to cNode(N1,N2), and
      // bNode(N1,Null) gets renamed to bNode(N1,Null), giving a match.
      val cv = new ComponentView(servers2, cNode(N1,N2), Array(bNode(N2,Null)))
      sysAbsViews.add(cv)
      assert(findReferencingView(conc, bNode(N1,Null), 3) == cv)
    }
    def test5 = {
      // println("= test5 =")
      reset()
      val conc = new Concretization(servers2, 
        Array(getDatumSt(T0,N1,N2), aNode(N1,N2), bNode(N2,Null), 
          getDatumSt(T1,N2,N3)))
      val st = cNode(N3, Null)
      assert(findReferencingView(conc, st, 3) == null)
      // Following fails, since T1's first reference should be to a B-node
      sysAbsViews.add(
        new ComponentView(servers2, getDatumSt(T1,N1,N2), 
          Array(cNode(N1,Null), cNode(N2, Null)) ))
      assert(findReferencingView(conc, st, 3) == null)
      // Following fails, since T1's first reference should be to a B-node
      // with null next reference.
      sysAbsViews.add(
        new ComponentView(servers2, getDatumSt(T1,N1,N2), 
          Array(bNode(N1,N3), cNode(N2, Null)) ))
      assert(findReferencingView(conc, st, 3) == null)
      // following succeeds, mapping T1->T1, N2->N1, N3->N2
      val cv = new ComponentView(servers2, getDatumSt(T1,N1,N2), 
          Array(bNode(N1,Null), cNode(N2, Null)) )
      sysAbsViews.add(cv)
      assert(findReferencingView(conc, st, 3) == cv)
    }
    def test6 = {
      // println("= test6 =")
      reset()
      val conc = new Concretization(servers2, 
        Array(getDatumSt(T0,N1,N2), aNode(N1,N2), bNode(N2,N3), 
          getDatumSt(T1,N2,N4)))
      val st = cNode(N4, Null)
      assert(findReferencingView(conc, st, 3) == null)
      // Following fails, since T1's first reference should be to a B-node
      sysAbsViews.add(
        new ComponentView(servers2, getDatumSt(T1,N1,N2), 
          Array(cNode(N1,N3), cNode(N2, Null)) ))
      assert(findReferencingView(conc, st, 3) == null)
      // Following fails, since T1's first reference should be to a B-node
      // with non-null next reference.
      sysAbsViews.add(
        new ComponentView(servers2, getDatumSt(T1,N1,N2), 
          Array(bNode(N1,Null), cNode(N2, Null)) ))
      assert(findReferencingView(conc, st, 3) == null)
      // Following fails, since T1's first reference should not point to T1's
      // second reference.
      sysAbsViews.add(
        new ComponentView(servers2, getDatumSt(T1,N1,N2), 
          Array(bNode(N1,N2), cNode(N2, Null)) ))
      assert(findReferencingView(conc, st, 3) == null)
      // following succeeds, mapping T1->T1, N2->N1, N3->N3, N4->N2
      val cv = new ComponentView(servers2, getDatumSt(T1,N1,N2), 
          Array(bNode(N1,N3), cNode(N2, Null)))
      sysAbsViews.add(cv)
      assert(findReferencingView(conc, st, 3) == cv)
    }

    println("== containsReferencingViewTest ==")
    test1; test2; test3; test4; test5; test6
  }


  private def isExtendableTest = {
    isExtendable(???, ???)
  }


  def test = {
    println("=== CheckerTest ===")
    effectOnTest
    compatibleWithTest
    containsReferencingViewTest
  }

}
