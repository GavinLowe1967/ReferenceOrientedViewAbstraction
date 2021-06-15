package ViewAbstraction

object MyStateMap{
  /** Mapping storing all the States found so far. */
  @volatile private var stateStore: StateMap = new InitialisationStateHashMap
    // if(UseTrieStateMap) new InitialisationStateHashMap else new ShardedStateMap

  // private var renewed = false

  /* We initially use a MyStateHashMap, but later transfer values into a
   * MyTrieStateMap (in renewStateStore).  This is because the latter
   * makes assumptions about various data structures being
   * initialised, but some States are created before this happens. */

  /** The number of States stored. */
  def stateCount = stateStore.size

  /** Factory method to either find existing state matching (family, cs,
    * ids), or to create new one. 
    * If existing state is returned, ids is recycled. */
  @inline 
  def apply(family: Int, cs: ControlState, ids: Array[Identity]): State =
    stateStore.getOrAdd(family, cs, ids)
    // assert(st.family == family); if(renewed) assert(stateStore.get(ix) == st)

  /** Factory method to either find existing state matching (family, cs,
    * ids), or to create new one, returning the State's index. 
    * If existing state is returned, ids is recycled. */
  @inline 
  def getByIndex(family: Int, cs: ControlState, ids: Array[Identity])
      : StateIndex = {
    val st = stateStore.getOrAddByIndex(family, cs, ids)
    // Note: there was a bug that made the following sometimes false.  I've
    // made stateStore volatile, as that might have been the issue.
    // 09/06/2020.
    assert(st != 0, 
           s"family = $family; cs = $cs; ids = "+ids.mkString("(", ",", ")"))
    st
  }
    // assert(st.family == family); if(renewed) assert(stateStore.get(ix) == st)

  /** The State with index ix. */
  @noinline def get(ix: StateIndex): State = stateStore.get(ix)

  /** Record that compilation is over. */
  def doneCompiling = 
    stateStore.asInstanceOf[InitialisationStateHashMap].doneCompiling
  // IMPROVE

  /** Replace the initial StateMap with a Trie-based one. 
    * Currently disabled. */
  def renewStateStore(numCS: Int, minCS: Int) = if(false){
    print("Creating Trie-based StateMap...")
    // IMPROVE following if just tsm used
    val it = stateStore.asInstanceOf[InitialisationStateHashMap].iterator.toArray
    // Entry i in it will receive index i+1
    val tsm = new MyTrieStateMap(numCS, minCS)
    // var i = 1
    for(st <- it){ tsm.add(st); /* assert(tsm.get(i) == st, i); i += 1 */ }
    assert(tsm.size == stateStore.size, s"${tsm.size}; ${stateStore.size}")
    if(true) stateStore = tsm // IMPROVE
    else{
      val tlshm = new ThreadLocalStateHashMap(tsm)
      for(i <- 0 until it.length) tlshm.add(it(i), i+1)
      stateStore = new ThreadLocalStateHashMaps(tlshm, tsm)
    }
    println(".  Done.")
  }

  /** Create an array containing all the states.  This is used only in
    * TestStates.report, and is normally not called. */
  def toArray = stateStore.asInstanceOf[InitialisationStateHashMap].toArray

  // import ox.gavin.profiling.MemoryProfiler.traverse  
  // def memoryProfile = {
  //   println(s"MyStateMap: $stateCount states")
  //   traverse("stateStore", stateStore, maxPrint = 2)
  // }


}
