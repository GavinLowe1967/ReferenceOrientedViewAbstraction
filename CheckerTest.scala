package ViewAbstraction

import scala.collection.mutable.{ArrayBuffer,HashSet}

class CheckerTest(system: SystemP.System, numWorkers: Int)
    extends Checker(system, numWorkers){
  import TestStates._

  def reset() = { 
    val (sav, initViews) = system.initViews //; sysAbsViews = sav
    checkerState = new CheckerState(system, sav)
    checkerState.initNextNewViews
  }

  reset()

  @inline private def sysAbsViews = checkerState.sysAbsViews
  @inline private def nextNewViews = checkerState.nextNewViews

  /** Test of effectOn. */
  private def effectOnTest = {
    // val effectOnO = new EffectOn(sysAbsViews, system)
    EffectOn.init(sysAbsViews, system)

    def effectOn(pre: Concretization, e: EventInt, post: Concretization, 
        cv: ComponentView) = {
      val trans = new Transition(pre, e, post)
      if(singleRef){
        if(useNewEffectOnStore) new NewEffectOn(trans, cv, nextNewViews)()
        else ??? // new SingleRefEffectOn(trans, cv, nextNewViews)()
      }
      else new EffectOn(trans, cv, nextNewViews)()
    }

    def mkCV(servers: ServerStates, princ: State, others: Array[State]) = {
      val cv = new ComponentView(servers, princ, others); /*cv.ply = 0;*/ cv
    }

    println("== effectOnTest ==")
    // transition on getLock.T0
    def test1 = {
      val pre = new Concretization(servers0, Array(initSt(T0)))
      val post = new Concretization(servers1, Array(gotLock(T0)))
      // pre.ply = 0; post.ply = 0
      // servers should evolve to servers1 on following two
      ply = 2
      effectOn(pre, 1, post, mkCV(servers0, initNode(N0), Array()))
      effectOn(pre, 1, post, mkCV(servers0, aNode(N1, Null), Array()))
      // println(nextNewViews.iterator.mkString("\n"))
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
      reset() 
      val serversA = ServerStates(List(lock1(T0), top(N0), wd0B))
      val pre = new Concretization(serversA, Array(setTopB(T0,N1), bNode(N1,N0)))
      val serversB = ServerStates(List(lock1(T0), top(N1), wd1))
      val post = new Concretization(serversB, Array(unlock(T0), bNode(N1,N0)))
      val serversB1 = ServerStates(List(lock1(T0), top(N0), wd1))
      // pre.ply = 0; post.ply = 0

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
      // cv1.ply = 1
      effectOn(pre, 1, post, cv1)
      // println("\n"+nextNewViews.mkString("\n"))
      // The two bNodes unify
      assert(nextNewViews.contains(
        new ComponentView(serversB1, pushSt(T1,N0), Array(bNode(N0,N1)))))
        // new ComponentView(serversB1, StateArray(Array(pushSt(T1,N0), bNode(N0,N1))))))
      // No unification
      assert(nextNewViews.contains(
        new ComponentView(serversB1, pushSt(T1,N1), Array(bNode(N1,N2)))))
      assert(nextNewViews.size == 6)
    }

    // Test with initialisation of node
    def test3 = {
      // println("= test3 =")
      reset(); assert(!singleRef)
      val pre = new Concretization(servers1, 
        Array(initNodeSt(T0,Null), initNode(N0)))
      // servers1 has reference to T0
      val post = new Concretization(servers1,
        Array(setTopB(T0,N0), bNode(N0,Null)))
      // Principal unifies with principal.  But we don't look for that if
      // !singleRef.
      val cv1 = new ComponentView(servers1, initNodeSt(T0,Null), Array())

      //val map0 = servers1.remappingMap1(cv1.getParamsBound)
      val unifs = Unification.allUnifs(pre, cv1) // .components)
      assert(unifs.isEmpty)
      // println("unifs = \n"+unifs.map{case (map,unifs) =>
      //   RemapperP.Remapper.show(map)+": "+unifs}.mkString("\n"))

      effectOn(pre, 1, post, cv1)        
      // println("\n"+nextNewViews.toList.mkString("\n"))
      // println(nextNewViews.size)
      assert(nextNewViews.size == 0)
      // assert(nextNewViews.contains(
      //   new ComponentView(servers1, Array(setTopB(T0,N0), bNode(N0,Null)))))
      // assert(nextNewViews.size == 1)

      // Principal unifies with secondary component.
      val cv2 = new ComponentView(servers1, initNode(N0))
      effectOn(pre, 1, post, cv2)        
      //println("\n"+nextNewViews.mkString("\n"))
      // With unification
      assert(nextNewViews.contains(
        new ComponentView(servers1, bNode(N0,Null))))
      // Without unification -- not included
      // assert(nextNewViews.contains(
      //   new ComponentView(servers1, Array(initNode(N0)))))
      assert(nextNewViews.size == 1)

      val cv3 = new ComponentView(servers1, aNode(N0,Null)) 
      effectOn(pre, 1, post, cv3)        
      //println("\n"+nextNewViews.mkString("\n"))
      // Without unification -- not included
      // assert(nextNewViews.contains(
      //   new ComponentView(servers1, Array(aNode(N0,Null)))))
      assert(nextNewViews.size == 1)
    }

    def test4 = {
      // Principal of cv unifies with process that changes state, and so gains
      // reference to another component c; parameters can be mapped to other
      // parameters of c.
      //println("= test4 =")
      reset()
      val pre = new Concretization(servers0, 
        Array(getDatumSt(T0, N0, N1), aNode(N0, N2), bNode(N1, N3)) )
      val post = new Concretization(servers0,
        Array(popSt(T0, N0, N1), dNode(N0, N1, N2), bNode(N1, N3)) )
      // pre.ply = 0; post.ply = 0
      val cv = new ComponentView(servers0,  Array(aNode(N0, N1), cNode(N1, N2)))
      // cv.ply = 1
      effectOn(pre, 1, post, cv)
      // The aNode in cv unifies with that in pre, and evolves to
      // dNode(N0,N1,N2), gaining a reference to N2.  The second parameter in
      // the cNode might be any one of N1, N3 (from the bNode) or N4 (fresh).
      //println(nextNewViews.iterator.mkString("\n"))
      for(x <- List(N1, N3, N4))
        assert(nextNewViews.contains(new ComponentView(servers0, 
          dNode(N0,N1,N2), Array(bNode(N1,N3), cNode(N2,x)) )))
      assert(nextNewViews.size == 3)
    }

    test1; test2; test3; test4
  }


  def test = {
    println("=== CheckerTest ===")
    effectOnTest
  }

}
