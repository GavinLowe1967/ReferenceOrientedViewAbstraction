package ViewAbstraction
import scala.collection.mutable.HashMap

/** A store of all the current MissingInfos.  
  * 
  * Note: we currently store just those in the mcDoneStore, which have no
  * MissingCommon.  But much of the code is set up to also support
  * MissingCommons.  */
object MissingInfoStore{
  /** Keys used in the mapping. */
  private class Key(val newView: ReducedComponentView,
      val missingViews: Array[ReducedComponentView]
      /*val missingCommon: Array[MissingCommon]*/){

    /** Equality is equality of non-null elements.  Note: each parameter is
      * expected to be sorted. */
    override def equals(that: Any) = that match{
      case k: Key =>
        k.newView == newView && 
        MissingInfo.equalExceptNull(k.missingViews, missingViews)//  && 
        // (if(missingCommon == null) k.missingCommon == null
        // else k.missingCommon != null &&
        //   MissingInfo.equalExceptNull(k.missingCommon, missingCommon) )
    }

    override def hashCode = 
      // MissingInfo.hashMC(newView, missingCommon, 0) ^ 
      MissingInfo.hashMV(missingViews, 0) ^ newView.hashCode
  } // end of Key

  /** Make a key.  Note: we need to clone the arrays, because of sharing. */
  @inline private def mkKey(newView: ReducedComponentView,
      missingViews: Array[ReducedComponentView],
      missingCommon: Array[MissingCommon] = null) = {
    assert(missingCommon == null)
    new Key(newView, missingViews.clone)
      //if(missingCommon == null) null else missingCommon.clone)
  }

  /** The number of shards used in the store. */
  private val numShards = powerOfTwoAtLeast(numWorkers) * 32

// IMPROVE: make the contains operation lock-free

// Improve: maybe purge when the newView in in the ViewSet

  /** The underlying store. */
  // private var store = new ShardedHashMap[Key, MissingInfo](shards = numShards)
  private var store = new MyShardedHashSet[Key](shards = numShards)

  /* Note: if two MissingInfos have the same newView, and the constraints of one
   * are a subset of those of another, then we aim not to include the latter.
   * We don't do this completely, as we don't purge supersets when we add a
   * new value.  Also, concurrent adds might not see the effect of the other.
   * However, this doesn't matter, as this is only a heuristic. */

  /** Does the store contain a MissingInfo for newView and a subset of
    * missingViews and missingCommon?  If strict = true, then only consider
    * strict subsets. */
  @inline private def containsSubset(newView: ReducedComponentView,
    missingViews: Array[ReducedComponentView], 
    missingCommon: Array[MissingCommon], strict: Boolean = false)
  : Boolean = {
    assert(missingCommon == null)
    assert(missingViews != null); val mvLength = missingViews.length
    val mcLength = if(missingCommon == null) 0 else missingCommon.length
    val length = mvLength + mcLength
    // Count number of non-nulls in missingViews, missingCommon
    var i = 0; var nonNulls = 0
    while(i < mvLength){ if(missingViews(i) != null) nonNulls += 1; i += 1 }
    i = 0
    while(i < mcLength){ if(missingCommon(i) != null) nonNulls += 1; i += 1}
    /* Consider each subset of missingViews and missingCommon.  flags represents
     * the subset
     * 
     *  {missingViews(i) | i <- [0..mvLength), flags(i)} U 
     *  {missingCommon(i) | i <- [0..mcLength), flags(mvLength+i)}.  
     * 
     * We only set entries in flags corresponding to non-null entries in
     * missingViews or missingCommon.  Considering flags as a number in
     * binary, iter is the corresponding Int.  We consider each value in turn.
     * found is true if we've found a subset.  Inv: we've considered each
     * subset up to and including flags/iters.  If strict, we omit the final
     * case, where flags gets set to all true, corresponding to MissingInfo and
     * MissingCommon. */
// IMPROVE: it's not clear that considering MissingCommon actually helps
    val flags = new Array[Boolean](length); var found = false 
    var iter = 0; val iterBound = if(strict) (1<<nonNulls)-2 else (1<<nonNulls)-1
    while(!found && iter < iterBound){
      // Advance flags to next subset.  In effect, we increment the number
      // represented by flags (in binary), but skipping over bits that
      // correspond to nulls in missingViews/missingCommon.  done1 is true
      // when we flip a bit to true, so there is no further carry to consider.
      var done1 = false; var i = 0; iter += 1
      /* Advance i to next non-null element of missingViews/missingCommon. */
      @inline def advance() = {
        while(i < mvLength && missingViews(i) == null) i += 1
        if(i >= mvLength)
          while(i < length && missingCommon(i-mvLength) == null) i += 1
      }
      advance()
      // Inv: i < length because iter < (1<<nonNulls)
      while(/*i < length && */ !done1){
        if(i < mvLength) assert(missingViews(i) != null) 
        else assert(missingCommon(i-mvLength) != null)
        flags(i) = !flags(i)
        if(flags(i)) done1 = true else{ i += 1; advance() }
      }
      assert(done1)
      if(done1){
        // The subset of missingViews corresponding to flags.
        val missingViews1 = Array.tabulate(mvLength)(j =>
          if(flags(j)) missingViews(j) else null)
        val missingCommon1 = 
          if(missingCommon == null) null
          else Array.tabulate(mcLength)(j =>
            if(flags(mvLength+j)) missingCommon(j) else null)
        val key = mkKey(newView, missingViews1, missingCommon1)
        if(store.contains(key)) found = true
      }
      // else assert(iter == iterBound)
      //else{ done = true; assert(iter == (1 << nonNulls), s"$iter $nonNulls") }
    }
    assert(found || iter == iterBound)
    found
  }

  /** Does the store contain a MissingInfo that represents a strict subset of
    * the constraints of mi? */
  // def containsStrictSubset(mi: MissingInfo): Boolean =
  //   containsSubset(mi.newView, mi.missingViews, mi.missingCommon, true)

  /** Add mi if there is no existing MissingInfo that represents a subset of the
    * constraints. */
  @inline def add(mi: MissingInfo): Boolean = {
    val newView = mi.newView
    val missingViews = mi.missingViews; val missingCommon = mi.missingCommon
    if(!containsSubset(newView, missingViews, missingCommon)){
      val key = mkKey(newView, missingViews, missingCommon)
      store.add(key) // += key -> mi //
      true
    }
    else{ mi.setNotAdded; false }
  }
// IMPROVE: better to construct the missingInfo here when first adding.

  /** Remove the entry corresponding to mi but using oldMissingViews; replace it
    * with mi if there is no subset. */
  def replace(mi: MissingInfo, oldMissingViews: Array[ReducedComponentView])
      : Boolean = {
    // Note: we try to make the remove and add as close together as possible. 
    val newView = mi.newView; val newMissingViews = mi.missingViews
    val missingCommon = mi.missingCommon
    val oldKey = mkKey(newView, oldMissingViews, missingCommon)
    if(!containsSubset(newView, newMissingViews, missingCommon)){
      val newKey = mkKey(newView, newMissingViews, missingCommon)
      store.remove(oldKey); store.add(newKey) // += newKey -> mi // ; 
      true
    }
    else{ store.remove(oldKey); false }
  }

  /** Remove mi from the store. */
  def remove(mi: MissingInfo) = 
    store.remove(mkKey(mi.newView, mi.missingViews, mi.missingCommon))

  /** If the store contains a MissingInfo representing a proper subset of mi,
    * then remove mi and return true.  Otherwise, return false, indicating mi
    * should be retained. */
  def removeIfProperSubset(mi: MissingInfo): Boolean = {
    val newView = mi.newView; val missingViews = mi.missingViews
    val missingCommon = mi.missingCommon
    if(containsSubset(newView, missingViews, missingCommon, true)){
      store.remove(mkKey(newView, missingViews, missingCommon)); true
    }
    else false
  }

  def size = store.size

  /** Reset for a new check. */
  def reset = store = new MyShardedHashSet[Key](shards = numShards)
  // new ShardedHashMap[Key, MissingInfo](shards = numShards)

}
