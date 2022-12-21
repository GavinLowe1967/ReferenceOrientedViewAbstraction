package ViewAbstraction
import collection.{OpenHashSet,ShardedHashMap,ShardedLockableMap}
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
    new ShardedLockableMap[ReducedComponentView, Array[MissingCrossReferences]]
    //new ShardedHashMap[ReducedComponentView, Array[MissingCrossReferences]]

  /** Minimum size to initialise an ArrayBuffer in byNewView.  Note: when an
    * ArrayBuffer is resized, it is to size at least 16; so a smaller initial
    * size might lead to higher memory consumption. */
  private val InitABSize = 8

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
    var done = false; var found = false
    // found is set to true if we find a MCR that implies mcr
    byNewView.acquireLock(newView)
    // val oldMCRs = 
    //   byNewView.getOrElseUpdate(newView, new Array[MissingCrossReferences](0))
    byNewView.get(newView, true) match{
      case None => 
        byNewView.add(newView, Array(mcr))
        byNewView.releaseLock(newView); true
      case Some(oldMCRs) =>
        var i = 0; done = true; val len = oldMCRs.length
        // Bitmap showing those MCRs not implied by mcr, and their count
        val include = new Array[Boolean](len); var count = 0
        while(i < len && !found){
          val mcr1 = oldMCRs(i); assert(mcr1 != mcr && !mcr1.isSuperseded)
          val cmp = MissingCrossReferences.compare(mcr, mcr1)
          if(cmp == Superset || cmp == Equal) found = true
          // Test if mcr1 is superceded by mcr
          if(cmp == Subset){ // mcr1 is superceded by mcr
            mcr1.setSuperseded
            // Profiler.count("NewEffectOnStore.shouldStore removed old")
          }
          else{ include(i) = true; count += 1 }
          i += 1
        } // end of while loop
        if(found && count == i){ // mcr is superseded, but none of the others is
          // No need to update byNewView
          byNewView.releaseLock(newView); false
        }
        else{
          // None of remainder can be superseded, so include them.
          while(i < len){ include(i) = true; count += 1; i += 1 }
          // Create new array holding retained elements of oldMCRs and maybe mcr
          val newLen = if(found) count else count+1
          val newMCRs = new Array[MissingCrossReferences](newLen)
          i = 0; var j = 0
          while(i < len){
            if(include(i)){ newMCRs(j) = oldMCRs(i); j += 1 }
            i += 1
          }
          assert(j == count)
          // Maybe add mcr, and replace oldMCRs with newMCRs.
          if(!found) newMCRs(count) = mcr
          byNewView.replace(newView, newMCRs, true)
          byNewView.releaseLock(newView)
          !found
        }
    } // end of match
  }


/*
  private def shouldStore(mcr: MissingCrossReferences): Boolean = {
    val newView = mcr.inducedTrans.newView
    var done = false; var found = false
    // found is set to true if we find a MCR that implies mcr
    while(!done){
      val oldMCRs = 
        byNewView.getOrElseUpdate(newView, new Array[MissingCrossReferences](0))
      oldMCRs.synchronized{
        if(mapsto(byNewView, newView, oldMCRs)){ 
          var i = 0; done = true; val len = oldMCRs.length
          // Bitmap showing those MCRs not implied by mcr, and their count
          val include = new Array[Boolean](len); var count = 0
          while(i < len && !found){
            val mcr1 = oldMCRs(i); assert(mcr1 != mcr)
            val cmp = MissingCrossReferences.compare(mcr, mcr1)
            // if(false && mcr1.allFound) // can purge mcr1 here
            //   assert(cmp != Subset && cmp != Equal)
            if(cmp == Superset || cmp == Equal) found = true
            // Test if mcr1 is superceded by mcr
            if(cmp == Subset){ // mcr1 is superceded by mcr
              mcr1.setSuperseded
              // Profiler.count("NewEffectOnStore.shouldStore removed old")
            }
// IMPROVE: can mcr1 be superseded here?
            else if(!mcr1.isSuperseded){ // retain mcr1: not superseded by mcr
              include(i) = true; count += 1
            }
            else assert(false)
            i += 1
          } // end of while loop
          // Prepare to purge remaining is superseded.
          while(i < len){
            val mcr1 = oldMCRs(i)
// IMPROVE if assertion holds
            assert(!mcr1.isSuperseded)
            if(!mcr1.isSuperseded){ 
              include(i) = true; count += 1
            }
            i += 1
          }
// IMPROVE: merge above loops
          // Create new array holding retained elements of oldMCRs and maybe mcr
          val newLen = if(found) count else count+1
          val newMCRs = new Array[MissingCrossReferences](newLen)
          i = 0; var j = 0
          while(i < len){
            if(include(i)){ newMCRs(j) = oldMCRs(i); j += 1 }
            i += 1
          }
          assert(j == count)
          // Maybe add mcr, and replace oldMCRs with newMCRs.
          if(!found) newMCRs(count) = mcr //  newMCRs += mcr
          byNewView.replace(newView, newMCRs)
          // else if(!found) ab += mcr 
          // else Profiler.count("NewEffectOnStore.shouldStore false")
          // if(false && !found) byNewView.get(newView) match{
          //   case None => assert(false, s"No record ")
          //   case Some(ab) => assert(ab.contains(mcr), s"Not found $mcr\n") 
          // }
        } // end of if(mapsto...)
        // otherwise go round the loop again
      } // end of synchronized block
    } // end of while loop
    !found
  }
 */


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
            else 
              // Note: we do not do the same checks here as in `add`, as mcr
              // was already in missingCrossRefStore.  In particular, that
              // would break the logic in shouldStore.
              addToStore(missingCrossRefStore, mcr.missingHead, mcr)
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
          val condCSat =  MissingCommonWrapper(newInducedTrans, views) == null
          Profiler.count("New MissingCrossReferences from allCompletions "+
            condCSat)
          val newMCR =
            new MissingCrossReferences(newInducedTrans, newMissingCRs, false)
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
  def purgeByNewView(views: ViewSet) = /*if(false)*/{
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
// IMPROVE
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
