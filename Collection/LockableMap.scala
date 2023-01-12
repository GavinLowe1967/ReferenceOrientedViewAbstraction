package ViewAbstraction.collection

import ox.gavin.profiling.Profiler

/** Trait for a lockable map.  This provides fairly standard concurrent map
  * operations, but also allows the mapping of a particular key to be locked.
  * Note that if B values are shared, they might also need to be locked. */
trait LockableMap[A, B]{

  /** Acquire the lock on `a`. */
  def acquireLock(a: A): Unit 

  /** Release the lock on `a`.  Pre: this thread holds the lock. */
  def releaseLock(a: A): Unit

  /** Get the value associated with `a`, if one exists; otherwise update it to
    * the value of `b`.  Pre: this thread holds the lock on `a`. */
  def getOrElseUpdate(a: A, b: => B): B

  /** Add the mapping a -> b to the map.  Pre: this thread holds the lock on
    * `a`.*/
  def add(a: A, b: B): Unit 

  /* Each of the operations below has a precondition: if withLock then this
   * thread holds the lock for `a`; otherwise it is assumed that no other
   * thread is using `a` (in cases where operations are being done by a single
   * thread per shard).  */

  /** Replace the mapping for `a` with `b`.  Pre: this thread holds the lock
    * for `a`. */
  def replace(a: A, b: B, withLock: Boolean): Unit

  /** Optionally get the value associated with `a`. */
  def get(a: A, withLock: Boolean): Option[B]

  /** Remove the mapping for `a`, optionally returning the value previously
    * associated with `a`.   */
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

/*
    /** List of which keys are locked by which threads.  Protected by 
      * synchronized blocks.  Note: we expect this list to be short.  */
    private var lockList = List[(A, Thread)]()

    /** Is a lock held on a? */
    @inline private def contains(a: A) = {
      var ll = lockList
      while(ll.nonEmpty && ll.head._1 != a)  ll = ll .tail
      ll.nonEmpty
    }

    /** Record that a is locked by th. */
    @inline private def add(a: A, th: Thread) = lockList ::= (a,th)

    /** Record that a is no longer locked by th. */
    @inline private def remove(a: A, th: Thread) = {
      val pair = (a, Thread.currentThread())
      require(lockList.contains(pair))
      lockList = lockList.filter(_ != pair)
    }
 */

    private var size = 16 // initial size

    private var lockedKeys = new Array[A](size)

    private var lockers = new Array[Thread](size)

    private var count = 0

    /* This represents that lockers(i) has lockedKeys(i) locked, for each i <-
     * [0..count). */

    /** Is a lock held on a? */
    @inline private def contains(a: A): Boolean = {
      var i = 0
      while(i < count && lockedKeys(i) != a) i += 1
      i < count
    }

    /** Record that a is locked by th. */
    @inline private def add(a: A, th: Thread) = {
      if(count == size){ // resize
        val oldLockedKeys = lockedKeys; val oldLockers = lockers
        val oldSize = size; size = size*2; lockedKeys = new Array[A](size);
        lockers = new Array[Thread](size)
        Profiler.count("LockableMap resize"+size)
        for(i <- 0 until oldSize){ 
          lockedKeys(i) = oldLockedKeys(i); lockers(i) = oldLockers(i)
        }
      }
      lockedKeys(count) = a; lockers(count) = th; count += 1
    }

    /** Record that a is no longer locked by th. */
    @inline private def remove(a: A, th: Thread) = {
      // Find the entry for a
      var i = 0; while(lockedKeys(i) != a) i += 1
      require(lockers(i) == th)
      if(i < count-1){
        lockedKeys(i) = lockedKeys(count-1); lockers(i) = lockers(count-1)
      }
      count -= 1
    }

    /** Lock key `a` by the current thread.  Block if another thread holds the
      * lock. */
    def lock(a: A): Unit = {
      val th = Thread.currentThread()
      synchronized{
        // Block if lockList contains an entry for a
        while(contains(a)){ Profiler.count("LockableMap.Lock wait"); wait() }
        add(a,th)
      }
    }

    /** Unlock key `a` by the current thread.  Pre: this thread has `a` 
      * locked. */
    def unlock(a: A): Unit = {
      // val pair = (a, Thread.currentThread())
      val th = Thread.currentThread()
      synchronized{
        remove(a, th)
        // require(lockList.contains(pair))
        // lockList = lockList.filter(_ != pair)
        notifyAll() // Signal to all blocked threads.  IMPROVE?
      }
    }

    /** If `withLock`, check that the current thread holds the lock on `a`;
      * otherwise check that no thread holds any lock. */
    def checkLock(a: A, withLock: Boolean) = 
      if(withLock){
        val th = Thread.currentThread; var i = 0
        synchronized{
          while(i < size && lockedKeys(i) != a) i += 1
          require(i < size && lockers(i) == th)
        }
      }
      else synchronized{ require(count == 0) }

/*
    /** If `withLock`, check that the current thread holds the lock on `a`;
      * otherwise check that no thread holds any lock. */
    def checkLock(a: A, withLock: Boolean) = 
      if(withLock){
        val pair = (a, Thread.currentThread())
        synchronized{ require(lockList.contains(pair)) }
      }
      else synchronized{ require(lockList.isEmpty) }
 */
  } // end of LockInfo

  /** Information about locking of shards. */
  private val lockInfo = Array.fill(shards)(new LockInfo)

  /** Release the lock on `a`.  Pre: this thread holds the lock. */
  def releaseLock(a: A): Unit = {
    val h = hashOf(a); val sh = shardFor(h); lockInfo(sh).unlock(a)
  }

  /** Acquire the lock on `a`. */
  def acquireLock(a: A): Unit = {
    val h = hashOf(a); val sh = shardFor(h); lockInfo(sh).lock(a)
  }

  /** Get the value associated with `a`, if one exists; otherwise update it to
    * the value of `b`.  This thread must hold the lock on a. */
  def getOrElseUpdate(a: A, b: => B): B = {
    val h = hashOf(a); val sh = shardFor(h)
    lockInfo(sh).checkLock(a, true) // check lock for a held
    getOrElseUpdate(a, b, h, sh) // now do the update
  }

  /** Add the mapping a -> b to the map.  Pre: this thread holds the lock on
    * `a`.*/
  def add(a: A, b: B): Unit = {
    val h = hashOf(a); val sh = shardFor(h)
    lockInfo(sh).checkLock(a, true) // check lock for a held
    add(a, b, h, sh)
  }

  /* Each of the operations below has a precondition: if withLock then this
   * thread holds the lock for `a`; otherwise it is assumed that no other
   * thread is using `a`.  */

  /** Replace the mapping for `a` with `b`.  */
  def replace(a: A, b: B, withLock: Boolean): Unit = {
    val h = hashOf(a); val sh = shardFor(h)
    lockInfo(sh).checkLock(a, withLock) // check lock usage
    replace(a, b, h, sh)
  }

  /** Optionally get the value associated with `a`. */
  def get(a: A, withLock: Boolean): Option[B] = {
    val h = hashOf(a); val sh = shardFor(h)
    lockInfo(sh).checkLock(a, withLock) // check lock usage
    get(a, h, sh)
  }

  /** Remove the mapping for `a`, optionally returning the value previously
    * associated with `a`.  */
  def remove(a: A, withLock: Boolean): Option[B] = {
    val h = hashOf(a); val sh = shardFor(h)
    lockInfo(sh).checkLock(a, withLock) // check lock usage
    remove(a, h, sh)
  }

}
