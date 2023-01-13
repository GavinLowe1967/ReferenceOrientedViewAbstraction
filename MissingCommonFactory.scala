package ViewAbstraction

import scala.collection.mutable.ArrayBuffer
import ox.gavin.profiling.Profiler

/** Object to create MissingCommons. */
object MissingCommonFactory{
  // ======================================= Storing of previous MissingCommons.

  private type Cpts = Array[State]

  /** Type of keys for storing MissingCommons. */
  private class Key(
    val ssIndex: Int, val cpts1: Array[State], val cpts2: Array[State],
    val pf: Int, val pId: Int
  ){
    override def hashCode = {
      val h1 = StateArray.mkHash1((ssIndex*71+pf)*71+pId, cpts1)
      StateArray.mkHash1(h1, cpts2)
    }

    override def equals(that: Any) = that match{
      case key: Key => 
        key.ssIndex == ssIndex && key.pf == pf && key.pId == pId &&
        key.cpts1.sameElements(cpts1) && key.cpts2.sameElements(cpts2)
    }
  }

  private def mkKey(
    servers: ServerStates, cpts1: Cpts, cpts2: Cpts, pid: ProcessIdentity) = 
    new Key(servers.index, cpts1, cpts2, pid._1, pid._2)

  import ViewAbstraction.collection.ShardedHashMap

  /** The type of the store of all MissingCommon we have created. */
  private type MissingCommonStore = ShardedHashMap[Key, MissingCommon]

  /** All the MissingCommon we have created.  Protected by a synchronized block
    * on itself.*/
  private var allMCs = new MissingCommonStore 

  /** Get the MissingCommon associated with key. */
  @inline private def getMC(key: Key) = allMCs.get(key)

  /** Store mc against key, unless there is already an associated value.  Return
    * the resulting stored value. */
  private def setOrGet(key: Key, mc: MissingCommon) = 
    allMCs.getOrElseUpdate(key, mc)

  // ======================================================= Main function

  /** A MissingCommon object, corresponding to servers, cpts1, cpts2 and pid, or
    * null if the obligation is already satisfied.  Here cpts1 corresponds to
    * the pre-state of a transition, and cpts2 to the view acted upon.
    * 
    * For each component state c with identity pid such that servers ||
    * cpts1(0) || c is in views, missingCandidates contains the list of Views
    * that are needed to satisfy the obligation but are currently missing from
    * views: (1) servers || cpts2(0) || c; and (2) if c has a reference to a
    * secondary component c2 of cpts1 or cpts2, then servers || c || c2
    * (renamed).
    * 
    * Pre: servers || cpts1 is in normal form.
    */
  def makeMissingCommon(
    servers: ServerStates, cpts1: Cpts, cpts2: Cpts, 
    pid: ProcessIdentity, views: ViewSet)
      : MissingCommon = {
    require(singleRef && cpts2.length == 2, StateArray.show(cpts2))
    val key = mkKey(servers, cpts1, cpts2, pid)
    getMC(key) match{
      case Some(mc) => 
        Profiler.count("old MissingCommon")
        if(mc.done) null else mc 
      case None => 
        // IMPROVE: can we avoid creating the MissingCommon if it will be done?
        val mc = new SimpleMissingCommon(servers, cpts1, cpts2, pid._1, pid._2)
        Profiler.count("new MissingCommon")
        val ab = new ArrayBuffer[Cpts]; val princ1 = cpts1(0); var found = false
        // All component states c with identity pid such that views contains
        // servers || princ1 || c
        val cs = allInstantiations(servers, princ1, pid, views); var i = 0
        // Update mc for each
        while(i < cs.length && !found){
          val c = cs(i); i += 1
          found = mc.updateMissingCandidates(c, views, ab)
        }
        if(found) mc.setDone
        // Store mc if no other thread has done likewise in the meantime
        val mc2 = setOrGet(key, mc)
        if(!(mc2 eq mc)){
          println("Creation of MissingCommon duplicated.");
          Profiler.count("duplicate MissingCommon")
        }
        if(mc2.done) null else mc2
    }
  }

  /** All component states cpt with identity pid such that views contains
    * servers || princ || cpt.  Pre: servers || princ is in normal form. */
  @inline def allInstantiations(
    servers: ServerStates, princ: State, pid: ProcessIdentity, views: ViewSet)
      : ArrayBuffer[State] = {
    val ab = new ArrayBuffer[State]; val iter = views.iterator(servers, princ)
    while(iter.hasNext){
      val cv = iter.next(); val cpts = cv.components;
      assert(cpts.length == 2, cv); val cpt = cpts(1)
      if(cpt.hasPID(pid)) ab += cpt
    }
    ab
  }

  // ======================================================= Purging

  private var shardIteratorProducer: 
       ShardedHashMap.ShardIteratorProducerT[Key, MissingCommon] = null

  def prepareForPurge = { shardIteratorProducer = allMCs.shardIteratorProducer }

  /** Purge MissingCommons that are done. */
  def purgeMCs() = { 
    var shardIterator = shardIteratorProducer.get
    while(shardIterator != null){
      while(shardIterator.hasNext){
        val (key,mc) = shardIterator.next(); if(mc.done) allMCs.remove(key)
      }
      shardIterator = shardIteratorProducer.get
    }
  }

  // ================================================Administrative functions

  def allMCsSize = allMCs.size

  /** Perform a memory profile of this. */
  def memoryProfile = {
    import ox.gavin.profiling.MemoryProfiler.traverse
    // Traverse 5 MissingCommons
    val iter = allMCs.valuesIterator
    for(_ <- 0 until 5; if iter.hasNext)
      traverse("MissingCommon", iter.next(), maxPrint = 3); println() 
    // allMCs
    println("MissingCommon.allMCs size = "+printInt(allMCs.size))
    traverse("allMCs", allMCs, maxPrint = 1); println()
    // the rest
    traverse("MissingCommon", this, maxPrint = 1); println()
  }

  /** Reset ready for a new check. */
  def reset =  allMCs = new MissingCommonStore

}
