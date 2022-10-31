package ViewAbstraction
import collection.{OpenHashSet,ShardedHashMap}
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

  /** A store, abstractly a set of (A,B) pairs.  Implemented as a map A => sets
    * of B. */
  private type Store[A, B <: AnyRef with ClassTag[B]] = 
    ShardedHashMap[A, OpenHashSet[B]]

  /* Maplets in each Store are updated by: (1) reading a -> bs; (2) locking bs;
   * (3) checking store still holds a -> bs; (4) updating bs, maybe replacing
   * it in the Store; (5) unlocking bs.  If (3) fails then re-try.
   * Alternatively, a maplet a -> bs can be removed by: (1) removing a
   * (optaining bs); (2) locking bs; (3) processing bs; (4) unlocking bs.  At
   * most one such remove may be performed for each a.  If a standard update
   * performs the locking before a remove, then the remove will see the effect
   * of the update.  */

  /** A store of MissingCrossReferences objects.  Each is stored against its
    * next missing view. */
  private val missingCrossRefStore = 
    new Store[ReducedComponentView, MissingCrossReferences]

  /** A store of MissingCrossReferneces objects for which there are no common
    * missing references, keyed against the new views they would produce. */
  private val byNewView = 
    new ShardedHashMap[ReducedComponentView, ArrayBuffer[MissingCrossReferences]]

  /** A store of MissingCommonWrapper objects.  Each is stored against its next
    * missing view. */
  private val missingCommonStore = 
    new Store[ReducedComponentView, MissingCommonWrapper]

  /** A store for MissingCommonWrapper objects.  Each is stored against the
    * servers and principal of the pre-state of the transition.  Given a new
    * view v, we match against (v.servers,v.principal), and try to use
    * v.components(1) to instantiate c.  */
  private val candidateForMCStore =
    new Store[(ServerStates, State), MissingCommonWrapper]

  /** Does store still hold key -> value? */
  @inline private 
  def mapsto[A, B <: AnyRef](store: ShardedHashMap[A, B], key: A, value: B)
      : Boolean =
    store.get(key) match{
      case Some(b) => b eq value // Note: reference equality
      case None => false
    }

  /** Add a -> b to store. */
  @inline private def addToStore[A, B <: AnyRef]
    (store: ShardedHashMap[A, OpenHashSet[B]], a: A, b: B)
    (implicit tag: ClassTag[B])
  = {
    var done = false
    while(!done){
      val set = store.getOrElseUpdate(a, mkSet[B])
      set.synchronized{
        if(mapsto(store, a, set)){ set.add(b); done = true }
        // Otherwise go round the loop again
      }
    }
  }

  /** Store missingCommonRefs in the missingCommonRefStore.  If condCSat then
    * check that missingCrossRefs is not implied by a current value in
    * byNewView; and if any there is implied by missingCrossRefs, then mark it
    * as superseded.  Pre: if condCSat then condition (c) must be satisfied
    * for missingCrossRefs. */
  def add(missingCrossRefs: MissingCrossReferences, condCSat: Boolean): Unit = {
    if(!condCSat || shouldStore(missingCrossRefs)){
      val missingHead = missingCrossRefs.missingHead
      addToStore(missingCrossRefStore, missingHead, missingCrossRefs)
    }
  } 

  /** Should mcr be stored, i.e. is it not implied by any prior
    * MissingCrossReferences object?  Pre: this has no missing common
    * references.  We check that no other such that would produce the same new
    * view has a subset of the missing views.  Also any other that has a
    * superset of mcr's missing views is marked as superseded (and removed
    * when purging).  */
  private def shouldStore(mcr: MissingCrossReferences): Boolean = {
    import MissingCrossReferences.{compare,Superset,Equal,Subset}
    val newView = mcr.inducedTrans.newView
    var done = false; var found = false
    // found is set to true if we find a MCR that implies mcr
    while(!done){
      val ab = byNewView.getOrElseUpdate(newView,
        new ArrayBuffer[MissingCrossReferences](1))
      ab.synchronized{
        if(mapsto(byNewView, newView, ab)){ 
          var i = 0; done = true
          // Those MCRs not implied bymcr
          val newAB = new ArrayBuffer[MissingCrossReferences](ab.length+1)
          while(i < ab.length && !found){
            val mcr1 = ab(i); i += 1; val cmp = compare(mcr, mcr1)
            if(cmp == Superset || cmp == Equal) found = true
            // Test if mcr1 is superceded by mcr
            if(cmp == Subset){ // mcr1 is superceded by mcr
              mcr1.setSuperseded
              Profiler.count("NewEffectOnStore.shouldStore removed old")
            }
            else newAB += mcr1 // retain mcr1: not superseded by mcr
          } // end of while loop
          if(newAB.length != ab.length){
            if(!found) newAB += mcr
            byNewView.replace(newView, newAB)
          }
          else if(!found) ab += mcr 
          else Profiler.count("NewEffectOnStore.shouldStore false")
        }
        // otherwise go round the loop again
      } // end of synchronized block
    } // end of while loop
    !found
  }

/*
  /** Remove mcr from missingCrossRefStore. */
  private def remove(mcr: MissingCrossReferences) = {
    val missingHead = mcr.missingHead; var done = false
    while(!done){
      missingCrossRefStore.get(missingHead) match{
        case Some(set) => 
          set.synchronized{
            if(mapsto(missingCrossRefStore, missingHead, set)){
              set.remove(mcr); done = true 
            }
          }
          // otherwise go round the loop
        case None => // This is possible if another thread removed mcr
          done = true
      }
    }
  }
 */

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
    missingCrossRefStore.remove(cv) match{
      case Some (mcrs) => mcrs.synchronized{
        // Note: cv < mcr.missingHead, so the MissingCrossRefSets are locked
        // in increasing order of their associated keys.
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
 
      // Note: if an addMissingCrossRef reads and checks the mapping cv ->
      // mcrs before this function removes cv, then this function will see the
      // effect of that add (because of the locking of mcrs).  There cannot be
      // another call to completeMissingCrossRefs with the same cv.

      case None => {}
    }
  }

  import InducedTransitionInfo.newMissingCrossRefs

  /** Deal with a MissingCrossReferences object that is done: either create and
    * store a corresponding MissingCommonWrapper, or fire the transition. */
  @inline private def doneMissingCrossRefs(
    mcr: MissingCrossReferences, views: ViewSet, result: ViewBuffer)
  = {
    require(mcr.done)
    val inducedTrans = mcr.inducedTrans

    //if(!lazyNewEffectOnStore){ ???
//       // Now deal with common missing references: add to relevant stores.
//       // IMPROVE: calculate the commonMissingPids here, rather than earlier
//       val mcw = MissingCommonWrapper(inducedTrans, mcr.commonMissingPids, views)
//       if(mcw != null) add(mcw)
//       else maybeAdd(inducedTrans, result) // can fire transition
    // }
    //else 
    if(mcr.candidates != null){
      val unflattened = CompressedCandidatesMap.splitBy(mcr.candidates, 
        inducedTrans.cv.getParamsBound)
      val map0 = CompressedCandidatesMap.extractMap(unflattened) //mcr.candidates)
      for(map <- mcr.allCompletions){
        // Instantiate oldCpts in inducedTrans
        val cpts = Remapper.applyRemapping(map, inducedTrans.cv.components)
        val newInducedTrans = inducedTrans.extend(cpts)
        // New missing cross references created by extending
        val newMissingCRs = newMissingCrossRefs(inducedTrans, map0, cpts, views)
// IMPROVE: recycle map0? 
        if(newMissingCRs.nonEmpty){ // Create new MissingCrossReferences object
          val newMCR =
            new MissingCrossReferences(newInducedTrans, newMissingCRs, null)
          add(newMCR, false)
        }
        else checkConditionC(newInducedTrans, views, result)
      }
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
    if(mcw != null) add(mcw)
    else maybeAdd(inducedTrans, result) // can fire transition
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
    missingCommonStore.remove(cv) match{
      case Some(mcws) => mcws.synchronized{
        for(mcw <- mcws.iterator) mcw.synchronized{
          assert(mcw.servers == cv.servers)
          if(!mcw.done && !mcw.isNewViewFound(views)){
            val cb = mcw.updateMissingViews(views); updateMCW(mcw, cb, result)
          }
        }
      } // end of mcws.synchronized

      case None => {}
    } // end of match
  }

  /** Try to complete values in candidateForMCStore based on cv. */
  private def completeCandidateForMC(
    cv: ComponentView, views: ViewSet, result: ViewBuffer)
      : Unit = {
    val key = (cv.servers, cv.principal)
    candidateForMCStore.get(key) match{
      case Some(mcws) => 
        var done = false
        mcws.synchronized{
          if(mapsto(candidateForMCStore, key, mcws)){
            val newMCWs = mkSet[MissingCommonWrapper] // values to retain
            done = true
            for(mcw <- mcws.iterator) mcw.synchronized{
              if(!mcw.done && !mcw.isNewViewFound(views)){
                val cb = mcw.updateWithNewMatch(cv, views)
                updateMCW(mcw, cb, result)
                if(!mcw.done) newMCWs.add(mcw)
              }
            }
            // Update the mapping for key
            val ok = 
              if(newMCWs.nonEmpty)
                candidateForMCStore.compareAndSet(key, mcws, newMCWs)
              else candidateForMCStore.removeIfEquals(key, mcws)
            assert(ok)
          }
        } // end of mcws.synchronized block

        if(!done){ // this raced with another operation, so retry
          Profiler.count("completeCandidateForMC retry")
          completeCandidateForMC(cv, views, result)
        }

      case None => {}
    }
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

  private var byNewViewShardIterator: ShardIteratorProducerT[
    ReducedComponentView, ArrayBuffer[MissingCrossReferences]]
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
  private def filter[A, B <: AnyRef]
    (key: A, set: OpenHashSet[B], p: B => Boolean, 
      store: ShardedHashMap[A, OpenHashSet[B]])
    (implicit tag: ClassTag[B])
  = {
    val iter = set.iterator; val newSet = mkSet[B]; var changed = false
    while(iter.hasNext){
      val x = iter.next(); if(p(x)) newSet += x else changed = true
    }
    if(changed){
      if(newSet.nonEmpty) store.replace(key, newSet) else store.remove(key)
    }
  }

  /** Purge done items from missingCrossRefStore. */
  def purgeMissingCrossRefStore(views: ViewSet) = {
    /** When is mcr retained?  When not done and not superseded. */
    def p(mcr: MissingCrossReferences) = !mcr.done(views) && !mcr.isSuperseded
    /* Purge from the maplet rv -> mcrs. */
    def process(
      rv: ReducedComponentView, mcrs: OpenHashSet[MissingCrossReferences]) 
    = filter(rv, mcrs, p _, missingCrossRefStore)

    missingCrossRefStoreShardIterator.foreach(process)
  }

  /** Purge items from byNewView. Remove items where the newView is found.  */
  def purgeByNewView(views: ViewSet) = {
    def process(
      nv: ReducedComponentView, ab: ArrayBuffer[MissingCrossReferences]) 
    = 
      if(views.contains(nv)){
        byNewView.remove(nv)
        Profiler.count("purgeByNewView removed")
      }

    byNewViewShardIterator.foreach(process)
  }

  def purgeMissingCommonStore(views: ViewSet) = {
    ???
  }

  // ================================ Administrative functions

  /** Report on the size of store. */
  def reportStore[A, B <: AnyRef](store: ShardedHashMap[A, OpenHashSet[B]])
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
    println("allMCs: size = "+printLong(MissingCommon.allMCsSize))
    print("missingCrossRefStore: "); reportStore(missingCrossRefStore)
    print("byNewView: "); reportByNewView()
    print("missingCommonStore: "); reportStore(missingCommonStore)
    print("candidateForMCStore: "); reportStore(candidateForMCStore)
  }

  /** Perform a memory profile of this. */
  def memoryProfile = {
    import ox.gavin.profiling.MemoryProfiler.traverse
    // profile MissingCommon, MissingInfoStore
    MissingCommon.memoryProfile

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
      val ab: ArrayBuffer[MissingCrossReferences] = abIter.next()
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
