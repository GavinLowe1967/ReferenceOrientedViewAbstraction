package ViewAbstraction

object MyStateMap{
  /** Mapping storing all the States found so far. */
  @volatile private var stateStore: StateMap = new InitialisationStateHashMap

  /* Note: initially the stateStore is an InitialisationStateHashMap, but we
   * replace it by a MyTrieStateMap after compilation is complete: the latter
   * needs to know the range of control states, and this information is
   * available only post-compilation. */

  /** Reset the stateStore.  Necessary when checking multiple files. */
  def reset = stateStore = new InitialisationStateHashMap

  /** The number of States stored. */
  def stateCount = stateStore.size

  /** Factory method to either find existing state matching (family, cs,
    * ids), or to create new one. 
    * If existing state is returned, ids is recycled. */
  @inline 
  def apply(family: Int, cs: ControlState, ids: Array[Identity]): State =
    stateStore.getOrAdd(family, cs, ids) 
  // synchronized{ stateStore.getOrAdd(family, cs, ids) }

  /** Replace the initial StateMap with a Trie-based one.  */
  def renewStateStore: Unit = {
    // return
    print("Creating Trie-based StateMap...")
    val it = stateStore.asInstanceOf[InitialisationStateHashMap].iterator
    // Entry i in it will receive index i+1
    val tsm = new MyTrieStateMap(State.numCS, State.minCS)
    var i = 1 // IMPROVE: remove assertions
    for(st <- it){ 
      tsm.add(st); assert(tsm.get(i) == st, i); i += 1
      // Initialise information about included parameters in st
      st.initIncludedParams 
    }
    assert(tsm.size == stateStore.size, s"${tsm.size}; ${stateStore.size}")
    stateStore = tsm 
    println(".  Done.")
  }

  /** Create an array containing all the states.  This is used only in
    * TestStates.report, and is normally not called. */
  def toArray = stateStore.iterator.toArray
}


