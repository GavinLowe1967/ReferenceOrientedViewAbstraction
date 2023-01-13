package ViewAbstraction
import collection.{OpenHashSet,ShardedHashMap,ShardedHashMap0,ShardedLockableMap}
import RemapperP.Remapper
import ox.gavin.profiling.Profiler
import scala.collection.mutable.ArrayBuffer
import scala.reflect.ClassTag

class NewEffectOnStore{
  require(singleRef)

  import RemappingExtender.CandidatesMap
  import SingleRefEffectOnUnification.commonMissingRefs

  import MissingCommonWrapper.{Cpts,CptsBuffer}
  // Array[State], Iterable[Cpts], resp

  /** Create an empty set of D's. */
  def mkSet[D <: AnyRef](implicit tag: ClassTag[D]) =
    new OpenHashSet[D](initSize = 8, ThresholdRatio = 0.6F)

  /** The number of shards to use in the stores below. */
  private val numShards = powerOfTwoAtLeast(numWorkers*8)

  /** A store, abstractly a set of (A,B) pairs.  Implemented as a map A => sets
    * of B. */
  private type Store[A, B <: AnyRef with ClassTag[B]] = 
    ShardedLockableMap[A, OpenHashSet[B]]

  /** A store of MissingCrossReferences objects.  Each is stored against its
    * next missing view. */
  private val missingCrossRefStore = 
    new Store[ReducedComponentView, MissingCrossReferences](shards = numShards)

  /** A store of MissingCrossReferneces objects for which there are no common
    * missing references, keyed against the new views they would produce. */
  private val byNewView = 
    new ShardedLockableMap[ReducedComponentView, Array[MissingCrossReferences]](
      shards = numShards)

  /** A store of MissingCommonWrapper objects.  Each is stored against its next
    * missing view. */
  private val missingCommonStore = 
    new Store[ReducedComponentView, MissingCommonWrapper](shards = numShards)

  /** A store for MissingCommonWrapper objects.  Each is stored against the
    * servers and principal of the pre-state of the transition.  Given a new
    * view v, we match against (v.servers,v.principal), and try to use
    * v.components(1) to instantiate c.  */
  private val candidateForMCStore =
    new Store[(ServerStates, State), MissingCommonWrapper](shards = numShards)

  /** Add a -> b to store. */
  @inline private def addToStore[A, B <: AnyRef]
    (store: ShardedLockableMap[A, OpenHashSet[B]], a: A, b: B)
    (implicit tag: ClassTag[B])
  = {
    store.acquireLock(a)
    val set = store.getOrElseUpdate(a, mkSet[B]); set.add(b)
    store.releaseLock(a)
  }

  /** Store missingCommonRefs in the missingCommonRefStore.  Check that
    * missingCrossRefs is not implied by a current value in byNewView; and if
    * any there is implied by missingCrossRefs, then mark it as
    * superseded.  
    * 
    * Pre: mcr is a new object, that no other thread will try to lock.*/
  def add(missingCrossRefs: MissingCrossReferences): Unit = {
    if(shouldStore(missingCrossRefs)){
      val missingHead = missingCrossRefs.missingHead
      addToStore(missingCrossRefStore, missingHead, missingCrossRefs)
    }
  } 

  import MissingCrossReferences.{Superset,Equal,Subset,Incomparable}

  /** Should mcr be stored, i.e. is it not implied by any prior
    * MissingCrossReferences object?  We check that no other such that would
    * produce the same new view has a subset of mcr's requirements for
    * conditions (b) and (c).  Also any other that has a superset of mcr's
    * requirements is marked as superseded (and removed when purging).
    * 
    * Pre: mcr is a new object, that no other thread will try to lock.  */
  private def shouldStore(mcr: MissingCrossReferences): Boolean = {
    val newView = mcr.inducedTrans.newView
    byNewView.acquireLock(newView)
    byNewView.get(newView, true) match{
      case None => 
        byNewView.add(newView, Array(mcr)); byNewView.releaseLock(newView); true
      case Some(oldMCRs) =>
        var i = 0; val len = oldMCRs.length; var found = false
        // found is set to true if we find a MCR that implies mcr.
        // Bitmap showing those MCRs not implied by mcr, and their count
        val include = new Array[Boolean](len); var count = 0
        while(i < len && !found){
          val mcr1 = oldMCRs(i); // assert(mcr1 != mcr && !mcr1.isSuperseded)
          val cmp = MissingCrossReferences.compare(mcr, mcr1)
          if(cmp == Superset || cmp == Equal) found = true
          if(cmp == Subset) mcr1.setSuperseded  // mcr1 is superceded by mcr
            // Profiler.count("NewEffectOnStore.shouldStore removed old")
          else{ include(i) = true; count += 1 }
          i += 1
        } // end of while loop
        if(found && count == i){ // mcr is superseded, but none of the others is
          // No need to update byNewView
          byNewView.releaseLock(newView); false
        }
        else{
          // None of remainder can be superseded, so include them.
          // while(i < len){ include(i) = true; count += 1; i += 1 }
          // We retain all of oldMCRs[i..len)
          count += len-i
          // Create new array holding retained elements of oldMCRs and maybe mcr
          val newLen = if(found) count else count+1; var k = 0
          val newMCRs = new Array[MissingCrossReferences](newLen); var j = 0
          while(k < len){
            if(k >= i || include(k)){ newMCRs(j) = oldMCRs(k); j += 1 }; k += 1
          }
          assert(j == count)
          // Maybe add mcr; replace oldMCRs with newMCRs; unlock.
          if(!found) newMCRs(count) = mcr
          byNewView.replace(newView, newMCRs, true)
          byNewView.releaseLock(newView)
          !found
        }
    } // end of match
  }

  /** Store mcw in missingCommonStore and candidateForMCStore. */
  def add(mcw: MissingCommonWrapper) = {
    require(!mcw.done)
    for(rv <- mcw.missingHeads) addToStore(missingCommonStore, rv, mcw)
    addToStore(candidateForMCStore, (mcw.servers, mcw.prePrincipal), mcw)
  }

  // ----------------- Operations to update values in the stores. 

  /** A set of ComponentViews, created by a call to complete.  These are views
    * that have been created by an induced transition. */
  type ViewBuffer = ArrayBuffer[ComponentView]

  /** Add the new view associated with inducedTrans to result if not already
    * there. */
  @inline private 
  def maybeAdd(inducedTrans: InducedTransitionInfo, buff: ViewBuffer) = {
    inducedTrans.markNewViewFound
    val v = inducedTrans.get
    if(!buff.contains(v)) buff += v else Profiler.count("maybeAdd repeat")
  }

  /** Try to complete values in missingCrossRefStore, based on the addition of
    * cv, and with views as the current ViewSet (i.e. from earlier plies).
    * Add any views that can now be added to result.  */
  private def completeMissingCrossRefs(
    cv: ComponentView, views: ViewSet, result: ViewBuffer)
  = {
    missingCrossRefStore.acquireLock(cv)
    missingCrossRefStore.remove(cv, true) match{
      case Some (mcrs) => /*mcrs.synchronized*/{
// IMPROVE: above synchronized not necessary? 
        for(mcr <- mcrs.iterator){
          var flag = false
          mcr.synchronized{
            if(!mcr.done && !mcr.isNewViewFound(views)){
              mcr.updateMissingViewsBy(cv, views); flag = true
            }
            // otherwise, we can ignore it
          } // end of mcr.synchronized block
          if(flag){
            if(mcr.done) doneMissingCrossRefs(mcr, views, result)
            else addToStore(missingCrossRefStore, mcr.missingHead, mcr)
          }
        } // end of iteration over mcrs/mcr.synchronized
      }
// IMPROVE: could store those mcr that we update, and then do the "if(flag)"
// part outside the mcrs.synchronized block

      case None => {}
    } // end of match
    missingCrossRefStore.releaseLock(cv)
  }

  import MissingCrossReferences.newMissingCrossRefs

  /** Deal with a MissingCrossReferences object that is done: either create and
    * store a corresponding MissingCommonWrapper, or fire the transition. */
  @inline private def doneMissingCrossRefs(
    mcr: MissingCrossReferences, views: ViewSet, result: ViewBuffer)
  = {
    require(mcr.done)
    val inducedTrans = mcr.inducedTrans
    if(mcr.candidates != null){
      val unflattened = CompressedCandidatesMap.splitBy(mcr.candidates, 
        inducedTrans.cv.getParamsBound)
      val map0 = CompressedCandidatesMap.extractMap(unflattened)
      val allComps = mcr.allCompletions
      // Profiler.count("NewEffectOnStore allCompletions "+allComps.length)
      // This doesn't contribute many instances.
      for(map <- allComps){
        // Instantiate oldCpts in inducedTrans
        val cpts = Remapper.applyRemapping(map, inducedTrans.cv.components)
        Pools.returnRemappingRows(map)
        val newInducedTrans = inducedTrans.extend(cpts)
        // New missing cross references created by extending
        val newMissingCRs = newMissingCrossRefs(inducedTrans, map0, cpts, views)
        if(newMissingCRs.nonEmpty){ // Create new MissingCrossReferences object
          // Test whether condition (c) is satisfied.  IMPROVE
          val condCSat = 
            MissingCommonWrapper.conditionCSatisfied(newInducedTrans, views)
            // MissingCommonWrapper(newInducedTrans, views) == null
          Profiler.count("New MissingCrossReferences from allCompletions "+
            condCSat)
          val newMCR =
            new MissingCrossReferences(newInducedTrans, newMissingCRs, condCSat)
// IMPROVE the false above?
          add(newMCR)
        }
        else checkConditionC(newInducedTrans, views, result)
      }
      Pools.returnRemappingRows(map0)
    }
    else{ 
      // Previously we considered a total map, so have considered all cross
      // references.  But condition (c) might not be satisfied if previously
      // we extended a map which produced new missing cross references *and*
      // common missing references.
      assert(mcr.candidates == null && inducedTrans.cpts != null,
        s"candidates: "+(mcr.candidates == null)+
          "; cpts: "+(inducedTrans.cpts == null))
      checkConditionC(inducedTrans, views, result)
    }
  }

  /** Check whether inducedTrans satisfies condition (c); either store a
    * MissingCommonWrapper or try adding the new view. */
  @inline private def checkConditionC(
    inducedTrans: InducedTransitionInfo, views: ViewSet, result: ViewBuffer) 
  = {
    val mcw = MissingCommonWrapper(inducedTrans, views)
    //if(/*true ||*/ mcw != null){
      if(mcw != null && !mcw.done) add(mcw)
      else maybeAdd(inducedTrans, result) // can fire transition
    //} // if mcr = null, subsumed
  }

  /** If mcw is now done, add the resulting views to result; otherwise register
    * against each element of cb. */
  @inline private 
  def updateMCW(mcw: MissingCommonWrapper, cb: CptsBuffer, result: ViewBuffer)
  = {
    if(cb == null){ assert(mcw.done); maybeAdd(mcw.inducedTrans, result) }
    else for(cpts <- cb){
      val rcv = ReducedComponentView(mcw.servers, cpts)
      addToStore(missingCommonStore, rcv, mcw)
    }
  }

  /** Try to complete values in missingCommonStore based on having found cv. */
  private def completeMissingCommons(
    cv: ComponentView, views: ViewSet, result: ViewBuffer)
  = {
    missingCommonStore.acquireLock(cv)
    missingCommonStore.remove(cv, true) match{
// mcws.synchronized necessary?  I think not
      case Some(mcws) => /*mcws.synchronized*/{
        for(mcw <- mcws.iterator) mcw.synchronized{
          assert(mcw.servers == cv.servers)
          if(!mcw.done && !mcw.isNewViewFound(views)){
            val cb = mcw.updateMissingViews(views); updateMCW(mcw, cb, result)
          }
        }
      } // end of mcws.synchronized

      case None => {}
    } // end of match
    missingCommonStore.releaseLock(cv)
  }

  /** Try to complete values in candidateForMCStore based on cv. */
  private def completeCandidateForMC(
    cv: ComponentView, views: ViewSet, result: ViewBuffer)
      : Unit = {
    val key = (cv.servers, cv.principal)
    candidateForMCStore.acquireLock(key)
    candidateForMCStore.get(key, true) match{
      case Some(mcws) => 
// IMPROVE: synchronized block necessary?  I think not
        /*mcws.synchronized*/{
          val newMCWs = mkSet[MissingCommonWrapper] // values to retain
          for(mcw <- mcws.iterator) mcw.synchronized{
            if(!mcw.done && !mcw.isNewViewFound(views)){
              val cb = mcw.updateWithNewMatch(cv, views)
              updateMCW(mcw, cb, result)
              if(!mcw.done) newMCWs.add(mcw)
            }
          }
          // Update the mapping for key
          if(newMCWs.nonEmpty) candidateForMCStore.replace(key, newMCWs, true)
          else candidateForMCStore.remove(key, true)
        } // end of mcws.synchronized block

      case None => {}
    }
    candidateForMCStore.releaseLock(key)
  }

  /** Try to complete values in the store, based on the addition of cv, and with
    * views as the current ViewSet (i.e. from earlier plies).  Return the
    * Views that can now be added.  */
  def complete(cv: ComponentView, views: ViewSet): ViewBuffer = {
    val result = new ViewBuffer
    completeMissingCrossRefs(cv, views, result)
    completeMissingCommons(cv, views, result)
    completeCandidateForMC(cv, views, result)
    result
  }

  // ================================ Purging

  import ShardedHashMap.ShardIteratorProducerT

  /** Object to produce iterators over the shards of missingCrossRefStore. */
  private var missingCrossRefStoreShardIterator: ShardIteratorProducerT[
    ReducedComponentView, OpenHashSet[MissingCrossReferences] ] 
  = null

  /** Object to produce iterators over the shards of missingCommonStore. */
  private var missingCommonStoreShardIterator: ShardIteratorProducerT[
    ReducedComponentView, OpenHashSet[MissingCommonWrapper] ] 
  = null

  /** Object to produce iterators over the shards of candidateForMCStore. */
  private var candidateForMCStoreShardIterator: ShardIteratorProducerT[
    (ServerStates, State), OpenHashSet[MissingCommonWrapper] ] 
  = null

  /** Object to produce iterators over the shards of byNextView. */
  private var byNewViewShardIterator: ShardIteratorProducerT[
    ReducedComponentView, Array[MissingCrossReferences]]
  = null

  /** Prepare for the next calls to purge. */
  def prepareForPurge = {
    missingCrossRefStoreShardIterator =
      missingCrossRefStore.shardIteratorProducer
    missingCommonStoreShardIterator = missingCommonStore.shardIteratorProducer
    candidateForMCStoreShardIterator = candidateForMCStore.shardIteratorProducer
    byNewViewShardIterator = byNewView.shardIteratorProducer
  }

  /** Filter `set` according to `p`, and update `store` so that `key` maps to
    * the new set (if non-empty). */
  // private def filter[A, B <: AnyRef]
  //   (key: A, set: OpenHashSet[B], p: B => Boolean, 
  //     store: ShardedHashMap[A, OpenHashSet[B]])
  //   (implicit tag: ClassTag[B])
  // = {
  //   val iter = set.iterator; val newSet = mkSet[B]; var changed = false
  //   while(iter.hasNext){
  //     val x = iter.next(); if(p(x)) newSet += x else changed = true
  //   }
  //   if(changed){
  //     if(newSet.nonEmpty) store.replace(key, newSet) else store.remove(key)
  //   }
  // }
// IMPROVE: remove above eventually

  private def filter[A, B <: AnyRef]
    (key: A, set: OpenHashSet[B], p: B => Boolean, 
      store: ShardedLockableMap[A, OpenHashSet[B]])
    (implicit tag: ClassTag[B])
  = {
    val iter = set.iterator; val newSet = mkSet[B]; var changed = false
    while(iter.hasNext){
      val x = iter.next(); if(p(x)) newSet += x else changed = true
    }
    if(changed){
      if(newSet.nonEmpty) store.replace(key, newSet, false) 
      else store.remove(key, false)
    }
  }

  /** Purge done items from missingCrossRefStore. */
  def purgeMissingCrossRefStore(views: ViewSet) = /*if(false)*/{
    /* When is mcr retained?  When not done and not superseded. */
    @inline def retain(mcr: MissingCrossReferences) = {
      val res = !mcr.done(views) && !mcr.isSuperseded
      if(!res) Profiler.count("MissingCrossReferences removed")
      res
    }
    /* Purge from the maplet rv -> mcrs. */
    @inline def process(
      rv: ReducedComponentView, mcrs: OpenHashSet[MissingCrossReferences]) 
    = filter(rv, mcrs, retain _, missingCrossRefStore)

    missingCrossRefStoreShardIterator.foreach(process)
  }

  /** Purge items from byNewView. Remove items where the newView is found.  */
  def purgeByNewView(views: ViewSet) = {
    def process(
      nv: ReducedComponentView, ab: Array[MissingCrossReferences]) 
    = {
      if(views.contains(nv)){
        byNewView.remove(nv, false)
        Profiler.count("purgeByNewView removed")
      }
      else{
        for(mcr <- ab) mcr.updateMissingViews(views)
        // If any MCR implies another, mark the latter as superseded.  NOTE:
        // this doesn't have a huge effect, marking around 10%, so might not
        // be worthwhile.
        var changed = false // has any been marked?
        for(i <- 0 until ab.length-1){
          val mcr1 = ab(i) 
          if(!mcr1.isSuperseded){
            for(j <- i+1 until ab.length){
              // IMPROVE:  while(!mcr1.isSuperseded)
              val mcr2 = ab(j); assert(mcr1 != mcr2)
              if(!mcr2.isSuperseded){
                val cmp = MissingCrossReferences.compare(mcr1,mcr2)
                if(cmp == Subset || cmp == Equal) mcr2.setSuperseded
                else if(cmp == Superset) mcr1.setSuperseded
                if(cmp != Incomparable){
                  changed = true; Profiler.count("purgeByNewView setSuperseded")
                }
              }
            }
          }
        } // end of for loop
        // Remove superseded values.
        if(changed){
          val newAB = new ArrayBuffer[MissingCrossReferences]
          for(mcr <- ab; if !mcr.isSuperseded) newAB += mcr
          byNewView.replace(nv, newAB.toArray, false)
          // IMPROVE: above record which are to be retained, and use Array
        }
      } // end of outer else

    }

    byNewViewShardIterator.foreach(process)
  }

  /** When is mcw retained?  When it's not done and its new view has not been
    * found. */
  @inline private def retain(mcw: MissingCommonWrapper, views: ViewSet) = {
    val res = !mcw.done && !mcw.isNewViewFound(views)
    if(!res) Profiler.count("MissingCommonWrapper removed")
    res
  }

  /** Purge values from missingCommonStore. */
  def purgeMissingCommonStore(views: ViewSet) = {
    /* Purge from the maplet rv -> mcws. */
    @inline def process(
      rv: ReducedComponentView, mcws: OpenHashSet[MissingCommonWrapper])
    = filter(rv, mcws, retain(_,views) , missingCommonStore)

    missingCommonStoreShardIterator.foreach(process)
  }

  /** Purge values from candidateForMCStore. */
  def purgeCandidateForMCStore(views: ViewSet) = {
    Profiler.count("purgeCandidateForMCStore")
    @inline def process(
      key: (ServerStates, State), mcws: OpenHashSet[MissingCommonWrapper])
    = filter(key, mcws, retain(_,views), candidateForMCStore)

    candidateForMCStoreShardIterator.foreach(process)
  }

  // ================================ Administrative functions

  /** Sanity check: every value in missingCrossRefStore that is not done, not
    * superseded, and that satisfied condition (c) is also in byNewView.  */
  def sanityCheck(views: ViewSet) = {
    println("Sanity check")
    for(mcrs <- missingCrossRefStore.valuesIterator; mcr <- mcrs.iterator)
      if(!mcr.done(views) && !mcr.isSuperseded && mcr.conditionCSatisfied){
        val nv = mcr.inducedTrans.newView
        byNewView.get(nv, false) match{
          case None => 
            assert(false, s"No record for $nv"+ mcr.isNewViewFound(views))
          case Some(ab) => assert(ab.contains(mcr), s"Not found $mcr\n"+
              mcr.isNewViewFound(views))
        }
      }
  }

  /** Report on the size of store. */
  def reportStore[A, B <: AnyRef](store: ShardedHashMap0[A, OpenHashSet[B]])
    (implicit tag: ClassTag[B])
  = {
    var keys = 0; var data = 0L
    for((_,set) <- store.iterator){ keys += 1; data += set.size }
    println(printInt(keys)+" keys; "+printLong(data)+" values")
  }

  def reportByNewView() = {
    var keys = 0; var data = 0L
    for((_,set) <- byNewView.iterator){ keys += 1; data += set.length }
    println(printInt(keys)+" keys; "+printLong(data)+" values")
  }

  /** Report on the size of the stores. */
  def report = {
    println("allMCs: size = "+printLong(MissingCommonFactory.allMCsSize))
    print("missingCrossRefStore: "); reportStore(missingCrossRefStore)
    print("byNewView: "); reportByNewView()
    print("missingCommonStore: "); reportStore(missingCommonStore)
    print("candidateForMCStore: "); reportStore(candidateForMCStore)
  }

  /** Perform a memory profile of this. */
  def memoryProfile = {
    import ox.gavin.profiling.MemoryProfiler.traverse
    // profile MissingCommon, MissingInfoStore
    MissingCommonFactory.memoryProfile

    // traverse N MissingCrossReferences
    val N = 5
    val setIter = missingCrossRefStore.valuesIterator; var count = 0
    while(count < N && setIter.hasNext){
      val set: OpenHashSet[MissingCrossReferences] = setIter.next()
      val iter = set.iterator
      while(count < N && iter.hasNext){
        traverse("MissingCrossReferences", iter.next(), maxPrint = 1); count += 1
      }
    }
    print("missingCrossRefStore: "); reportStore(missingCrossRefStore)
    traverse("missingCrossRefStore", missingCrossRefStore); println()
    // traverse N elements of byNewView
    val abIter = byNewView.valuesIterator; count = 0
    while(count < N && abIter.hasNext){
      val ab: Array[MissingCrossReferences] = abIter.next()
      println("ArrayBuffer length = "+ab.length)
      traverse("ArrayBuffer[MissingCommonReferences]", ab, maxPrint = 2)
      count += 1
    }

    print("byNewView: "); reportByNewView()
    traverse("byNewView", byNewView); println()

    // Traverse N MissingCommonWrappers
    val setIter1 = missingCommonStore.valuesIterator;  count = 0
    while(count < N && setIter1.hasNext){
      val set: OpenHashSet[MissingCommonWrapper] = setIter1.next()
      val iter = set.iterator
      while(count < N && iter.hasNext){
        traverse("MissingCommonWrapper", iter.next(), maxPrint = 1); count += 1
      }
    }
    print("missingCommonStore: "); reportStore(missingCommonStore)
    traverse("missingCommonStore", missingCommonStore); println()
    print("candidateForMCStore: "); reportStore(candidateForMCStore)
    traverse("candidateForMCStore", candidateForMCStore); println()
  }
}
