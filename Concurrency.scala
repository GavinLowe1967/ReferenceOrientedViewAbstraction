package ViewAbstraction

// import java.util.concurrent.Semaphore

/** Various concurrency primitives. */
object Concurrency{


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

// ==================================================================

import scala.collection.mutable.ArrayBuffer 

/** A concurrent buffer holding data of type A, to be used by numThreads
  * threads. */
class ConcurrentBuffer[A: scala.reflect.ClassTag ](numThreads: Int){
  /** ArrayBuffers holding the data, indexed by thread ids. */
  private val buffers = Array.fill(numThreads)(new ArrayBuffer[A])

  /** Add x, performed by thread me. */
  def add(me: Int, x: A) = buffers(me) += x

  /** Get an array holding all the data. */
  def get: Array[A] = {
    var i = 0; var size = 0 // size = total number of values
    while(i < numThreads){ size += buffers(i).length; i += 1 }
    val result = new Array[A](size); var ix = 0; i = 0
    while(i < numThreads){
      val thisBuff = buffers(i); var j = 0
      while(j < thisBuff.length){
        result(ix) = thisBuff(j); ix += 1; j += 1
      }
      i += 1
    }
    assert(ix == size)
    result
  }

}
