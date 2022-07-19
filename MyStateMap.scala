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
    //synchronized{ stateStore.getOrAdd(family, cs, ids) }

  /** Factory method to either find existing state matching (family, cs,
    * ids), or to create new one, returning the State's index. 
    * If existing state is returned, ids is recycled. */
  // @inline 
  // def getByIndex(family: Int, cs: ControlState, ids: Array[Identity])
  //     : StateIndex = {
  //   val st = synchronized{ stateStore.getOrAddByIndex(family, cs, ids) }
  //   // Note: there was a bug that made the following sometimes false.  I've
  //   // made stateStore volatile, as that might have been the issue.
  //   // 09/06/2020.
  //   assert(st != 0, 
  //          s"family = $family; cs = $cs; ids = "+ids.mkString("(", ",", ")"))
  //   st
  // }

  /** Record that compilation is over. */
  // def doneCompiling = 
  //   stateStore.asInstanceOf[InitialisationStateHashMap].doneCompiling
  // IMPROVE

  /** Replace the initial StateMap with a Trie-based one.  */
  def renewStateStore = {
    print("Creating Trie-based StateMap...")
    val it = stateStore.asInstanceOf[InitialisationStateHashMap].iterator
    // Entry i in it will receive index i+1
    val tsm = new MyTrieStateMap(State.numCS, State.minCS)
    var i = 1 // IMPROVE: remove assertions
    for(st <- it){ tsm.add(st); assert(tsm.get(i) == st, i); i += 1  }
    assert(tsm.size == stateStore.size, s"${tsm.size}; ${stateStore.size}")
    stateStore = tsm 
    println(".  Done.")
  }

  /** Create an array containing all the states.  This is used only in
    * TestStates.report, and is normally not called. */
  def toArray = stateStore.iterator.toArray
  //def toArray = stateStore.asInstanceOf[InitialisationStateHashMap].toArray

}

// ==================================================================

// All dead code below here, but we might want to resurrect it.

/*
    // assert(st.family == family); if(renewed) assert(stateStore.get(ix) == st)

  /** The State with index ix. */
  @noinline def get(ix: StateIndex): State = stateStore.get(ix)
 */


/*
  /* Previously, we initially used a MyStateHashMap, but later transfer values
   * into a MyTrieStateMap (in renewStateStore).  This is because the latter
   * makes assumptions about various data structures being initialised, but
   * some States are created before this happens. */

 */



