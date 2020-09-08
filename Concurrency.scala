package ViewAbstraction

import java.util.concurrent.Semaphore

/** Various concurrency primitives. */
object Concurrency{

  /** A barrier synchronisation using semaphores.
    * Based on Bernard's re-implementation of my implementation. */
  class Barrier(n: Int){
    // assert(n > 1)
    private [this] var waiting = 0 // number of processes currently waiting
    private [this] val wait    = new Semaphore(1); wait.acquire()
    private [this] val enter   = new Semaphore(1)
    // enter is up iff a new batch of processes can enter the barrier.
    // each entering process but the last is stalled by wait.

    /** Wait until all `n` processes have called sync */
    def sync(): Unit = if(n > 1){
      enter.acquire()
      if (waiting == n-1)    // the last process arrives
        wait.release()     // everyone can proceed (but cannot re-enter)
      else{                 // a process arrives that isn't the last
        waiting += 1; enter.release(); wait.acquire()         // make it wait
        waiting -= 1
        if (waiting == 0) enter.release()  // the last waiting process awoke
        else wait.release()              // pass the baton to another waiter
      }
    }
  }

  /** A barrier synchronisation, based on atomic variables.  
    * This seems slower than the semaphore version. */
  class AtomicBarrier(n: Int){
    import java.util.concurrent.atomic.AtomicInteger
    // Number who have called sync on this round
    private [this] val waiting = new AtomicInteger(0)
    // Number who have registered their leaving for this round
    private [this] val left = new AtomicInteger(0)

    def sync(): Unit = {
      // Wait for previous round to finish
      while(left.get > 0){ }
      // Register
      val myW = waiting.getAndIncrement; assert(myW <= n)
      // Wait for others
      while(waiting.get < n){ }
      // Leaving phase
      var done = false
      do{
        val myLeft = left.get
        if(myLeft < n-1) done = left.compareAndSet(myLeft, myLeft+1)
        else{ // I'm the last thread; reset for next round
          assert(waiting.get == n)
          assert(left.get == n-1)
          waiting.set(0); left.set(0); done = true
        }
      }while(!done)
    }
  }

  // Parallelism helpers

  /** Create a thread that performs comp */
  private def mkThread(comp: => Unit) : Thread = 
    new Thread(new Runnable{ def run = comp })

  /** Create a system of processes `proc` for `i <- [0..p)`; run that system,
    * terminating when all the processes terminate. */
  def runSystem(p: Int, proc: => Unit) = {
    val threads = Array.fill(p)(mkThread(proc))
    threads.foreach(_.start)
    threads.foreach(_.join)
  }  

  /** Create a system of processes `proc(i)` for `i <- [0..p)`; run that system,
    * terminating when all the processes terminate. */
  def runIndexedSystem(p: Int, proc: Int => Unit) = {
    val threads = Array.tabulate(p)(i => mkThread(proc(i)))
    threads.foreach(_.start)
    threads.foreach(_.join)
  }


}

