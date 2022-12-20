package ViewAbstraction.collection

/** Trait for a lockable map.  This provides fairly standard concurrent map
  * operations, but also allows the mapping of a particular key to be locked.
  * Note that if B values are shared, they might also need to be locked. */
trait LockableMap[A, B]{
  /** Get the value associated with `a`, if one exists; otherwise update it to
    * the value of `b`.  Also lock the mapping for `a`. */
  def getOrElseUpdateAndLock(a: A, b: => B): B

  /** Release the lock on `a`.  Pre: this thread holds the lock. */
  def releaseLock(a: A): Unit

  /** Replace the mapping for `a` with `b`.  Pre: this thread holds the lock
    * for `a`. */
  def replace(a: A, b: B): Unit

  /** Remove the mapping for `a`, optionally returning the value previously
    * associated with `a`.  
    * 
    * Pre: if withLock then this thread holds the lock for `a`; otherwise it
    * is assumed that no other thread is using `a`. */
  def remove(a: A, withLock: Boolean): Option[B]
}

// ==================================================================

import scala.reflect.ClassTag

/** An implementation of LockableMap using sharding. */
class ShardedLockableMap[A, B](shards: Int = 128, initLength: Int = 32)
  (implicit tagA: ClassTag[A], tagB: ClassTag[B])
    extends ShardedHashMap0(shards, initLength)(tagA, tagB)
    with LockableMap[A, B]{

  import DeletableMap.hashOf   

  /** Information about the locking within a particular shard. */
  private class LockInfo{
    import java.lang.Thread

    /** List of which keys are locked by which threads.  Protected by 
      * synchronized blocks.  Note: we expect this list to be short.  */
    private var lockList = List[(A, Thread)]()

    /** Lock key `a` by the current thread.  Block if another thread holds the
      * lock. */
    def lock(a: A): Unit = {
      val th = Thread.currentThread()
      synchronized{
        // Block if lockList contains an entry for a
        while(lockList.exists(pair => pair._1 == a)) wait()
        lockList ::= (a,th)
      }
    }

    /** Unlock key `a` by the current thread.  Pre: this thread has `a` 
      * locked. */
    def unlock(a: A): Unit = {
      val pair = (a, Thread.currentThread())
      synchronized{
        require(lockList.contains(pair))
        lockList = lockList.filter(_ != pair)
        notifyAll() // Signal to all blocked threads.  IMPROVE?
      }
    }

    /** Check that the current thread holds the lock on `a`.  Throw an 
      * exception if not. */
    def checkLock(a: A) = {
      val pair = (a, Thread.currentThread())
      synchronized{ require(lockList.contains(pair)) }
    }
  } // end of LockInfo

  /** Information about locking of shards. */
  private val lockInfo = Array.fill(shards)(new LockInfo)

  /** Get the value associated with `a`, if one exists; otherwise update it to
    * the value of `b`.  Also lock the mapping for `a`. */
  def getOrElseUpdateAndLock(a: A, b: => B): B = {
    val h = hashOf(a); val sh = shardFor(h)
    lockInfo(sh).lock(a) // obtain the lock for a
    getOrElseUpdate(a, b, h, sh) // now do the update
  }

  /** Release the lock on `a`.  Pre: this thread holds the lock. */
  def releaseLock(a: A): Unit = {
    val h = hashOf(a); val sh = shardFor(h); lockInfo(sh).unlock(a)
  }

  /** Replace the mapping for `a` with `b`.  Pre: this thread holds the lock
    * for `a`. */
  def replace(a: A, b: B): Unit = {
    val h = hashOf(a); val sh = shardFor(h)
    lockInfo(sh).checkLock(a) // check this thread has a locked
    replace(a, b, h, sh)
  }

  /** Remove the mapping for `a`, optionally returning the value previously
    * associated with `a`.  
    * 
    * Pre: if withLock then this thread holds the lock for `a`; otherwise it
    * is assumed that no other thread is using `a`. */
  def remove(a: A, withLock: Boolean): Option[B] = {
    val h = hashOf(a); val sh = shardFor(h)
    if(withLock) lockInfo(sh).checkLock(a) // check this thread has a locked
    remove(a, h, sh)
  }

}
