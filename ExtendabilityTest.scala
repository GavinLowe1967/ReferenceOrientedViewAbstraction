package ViewAbstraction.ExtendabilityP

import ViewAbstraction._

class ExtendabilityTest(system: ViewAbstraction.SystemP.System){

  import TestStates._

  private var sysAbsViews: ViewSet = _

  /** Extendability object to test. */
  private var extendability: Extendability = _

  def reset() = { 
    val (sav, initViews) = system.initViews; sysAbsViews = sav
    extendability = new Extendability(sysAbsViews)
  }

  reset()

  /** Wrapper around Extendability.compatibleWith. */
  private def compatibleWith(pre: Concretization, st: State) =
    extendability.compatibleWith(pre, st)

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


  // import ExtendabilityP.Extendability.findReferencingView

  def findReferencingView(pre: Concretization, st: State, j : Int) = 
    extendability.findReferencingView(pre, st, j)

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

  // private def isExtendableTest = {
  //   isExtendable(???, ???)
  // }

  def test = {
    println("===ExtendabilityTest===")

    containsReferencingViewTest
    compatibleWithTest
  }

}
