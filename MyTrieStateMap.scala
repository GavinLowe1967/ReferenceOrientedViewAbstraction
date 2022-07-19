package ViewAbstraction

/** An implementation of a StateMap based upon a trie. 
  * @param numCS the number of control states. */
// Not currently used
class MyTrieStateMap(numCS: Int, minCS: Int) extends StateMap{
  println(s"MyTrieStateMap($numCS, $minCS)")

  /** A Trie for each control state, offset by minCS. */
  private var tries = new Array[Trie](numCS)

  /* Each access to tries is synchronized on tries.  Each access to the
   * array from a MidTries or StateArrayTries is synchronized on that
   * array.  
   * 
   * Each entry is written at most once, changing it from null to
   * non-null.  Therefore a read of a non-null value does not require
   * obtaining the lock.  It's only necessary to obtain the lock if it
   * appears necessary to write a value.  However, in such cases it's
   * necessary to re-read the entry, to ensure another thread hasn't
   * set it to a non-null value.  This tactic speeds up the getOrAdd
   * operation by a factor of about 50! */ 

  /** The index in tries to use for control state cs. */
  @inline private def indexForCS(cs: ControlState) = cs-minCS

  /* Each element of tries might be a StateTrie, corresponding to a
   * state with no parameters.  Otherwise, it is a tree of Tries, with
   * StateArrayTries at the bottom (at depth the arity of the control
   * state), and MidTries at every other depth.  
   * 
   * At the top level, the trie is indexed by control states, offset
   * by minCS, to allow for negative values.
   * 
   * At lower levels, each trie is index by the values of *two* identities (or
   * maybe one identity for the last ply), offset to allow for distinguished
   * values.  See function indexFor in getOrAdd.
   */

  /** The number of states created. */
  private val stateCount = new java.util.concurrent.atomic.AtomicInteger(0)

  /** The maximum fresh value allowed in any state.  FIXME.  I think the max
    * number of parameters of the same type in any state will suffice. */
  private val MaxFresh = 4

  /** sizeFor(indexForCS(cs))(index) gives the number of values allowed for the
    * parameter at position index in control state cs.  It equals
    * superTypeSizes(State.stateTypeMap(cs)(index)) + MaxFresh. */
  private val sizeFor0 = Array.tabulate(numCS){ csi => 
    val types = State.stateTypeMap(csi+minCS)
    if(types != null) types.map(superTypeSizes(_)+MaxFresh)
    else null
    // the +MaxFresh above is to allow for identities mapped to values not in
    // the script
  }

  // ----- The global array of states. 

  /** Array holding all states found so far.  Note: each state should be placed
    * in this array before being added to the trie. */
  @volatile private var allStates = new Array[State](1024)
  
  /** The number of States stored in allStates. */
  private var allStatesCount = 0
  /* The states are held in allStates[1..allStatesCount].  No state receives
   * index 0. */

  /** Lock protecting allStates and allStatesCount. */
  private val allStatesLock = new AnyRef

  /** Store st in allStates, returning index used.  IMPROVE: make more
    * efficient. */
  @inline private 
  def addToArray(st: State): StateIndex = allStatesLock.synchronized{
    if(allStatesCount+1 == allStates.length){ // resize
      val newAllStates = new Array[State](2*allStates.length)
      for(i <- 1 to allStatesCount) newAllStates(i) = allStates(i)
      allStates = newAllStates
    }
    allStatesCount += 1; allStates(allStatesCount) = st
    allStates = allStates // volatile write; publish
    allStatesCount
  }

  // IMPROVE: consider using sharding, and using locking for gets. 

  /** The state in position ix of the global array. */
  def get(ix: StateIndex) = allStates(ix) // read of allStates is subscribe

  // ----- Adding operations. 

  /** Get the state corresponding to cs and ids, creating it if necessary. */
  @inline def getOrAdd(family: Int, cs: ControlState, ids: Array[Identity])
      : State = {
    val ix = getOrMaybeAdd(family, cs, ids, null) 
    allStates(ix)
    // assert(newState.cs == cs && newState.ids.sameElements(ids)) 
  }  


  /** offSets(cs-minCS)(index) holds the number of distinguished values in the
    * type of the parameter index of cs. */
  private val offSets = 
    Array.tabulate(numCS){ cs => 
      val types = State.stateTypeMap(cs+minCS)
      if(types != null) types.map(distinguishedSizes)
      else null 
    }

  /** Get the state corresponding to cs and ids, and its index; if none is
    * stored, set it to addState if non-null, or create a new state. */
  @inline private def getOrMaybeAdd(
    family: Int, cs: ControlState, ids: Array[Identity], addState: State)
      : StateIndex /* (State, StateIndex) */ = { 
    val len = ids.length
    val csIndex = indexForCS(cs)
    // offset into tries for normal values
    val theOffsets = offSets(csIndex)
    // sizes of ranges for parameters
    val theSizes = sizeFor0(csIndex)

    // The contribution to the index into a trie corresponding to the
    // parameter at position index
    @inline def indexFor0(index: Int) = {
      val id = ids(index)
      // Second term below is the number of distinguished values of
      // the type of this identity, so gives an offset in each trie
      id + theOffsets(index)
    }

    // Index into a trie corresponding to the parameters at positions idsIndex
    // and indIndex+1
    @inline def indexFor(idsIndex: Int) = 
      if(idsIndex == len-1) indexFor0(idsIndex)
      else indexFor0(idsIndex) * theSizes(idsIndex+1) + indexFor0(idsIndex+1)

    // Size for the trie corresponding to the parameters at positions idsIndex
    // and indIndex+1
    @inline def sizeFor(cs: ControlState, idsIndex: Int) = {
      // assert(idsIndex < len, s"idsIndex = $idsIndex; len = $len")
      if(idsIndex == len-1) theSizes(idsIndex)
      else theSizes(idsIndex) * theSizes(idsIndex+1)
    }

    var trie: Trie = null

    if(len == 0){
      trie = tries(csIndex)
      if(trie == null){
        val newState = 
          if(addState == null) new State(family, cs, ids) else addState
        tries.synchronized{
          if(tries(csIndex) == null){
            val myIndex = addToArray(newState)
            tries(csIndex) = StateTrie(newState, myIndex)
            stateCount.getAndIncrement; myIndex 
          }
          else{
            println("**Newly created**");
            tries(csIndex).asInstanceOf[StateTrie].getIndex
          }
        } // end of synchronized block
      } // end of if(trie == null)
      else trie.asInstanceOf[StateTrie].getIndex
    } // end of if(len == 0)
    else{
      trie = tries(csIndex)
      if(trie == null){ // Create trie for this ControlState
        val newSize = sizeFor(cs, 0)
        trie = if(len <= 2) new StateArrayTrie(newSize) else new MidTrie(newSize)
        tries.synchronized{
          if(tries(csIndex) == null) tries(csIndex) = trie
          else trie = tries(csIndex) // recently written
        } // end of synchronized
      } // end of if trie == null

      // Iterate down to bottom level, creating new Tries as necessary
      var idsIndex = 0 // index into ids
      while(idsIndex < len-2){
        val nextTries = trie.asInstanceOf[MidTrie].tries
        val index = indexFor(idsIndex); trie = nextTries(index)
        if(trie == null){
          val newSize = sizeFor(cs, idsIndex+2)
          trie =
            if(idsIndex >= len-4) new StateArrayTrie(newSize)
            else new MidTrie(newSize)
          nextTries.synchronized{
            if(nextTries(index) == null) nextTries(index) = trie
            else trie = nextTries(index) // recently written
          } // end of synchronized
        }
        idsIndex += 2
      }

      // Get or create and store State in bottom level Trie
      val sat = trie.asInstanceOf[StateArrayTrie]
      val index = indexFor(idsIndex)  // assert(index < states.length)
      val (st, myIndex) = sat.get(index) 
      // Note: need both checks in following line in case call so sat.get is
      // concurrent with a write (or use sat.synchronized in above line, but
      // that slows things down).
      if(st != null && myIndex != 0) myIndex 
      else{
        val newState = 
          if(addState == null) new State(family, cs, ids) else addState
        sat.synchronized{
          val (st1,myIndex1) = sat.get(index)
          if(st1 != null) myIndex1
          else{ 
            val myIndex = addToArray(newState); assert(myIndex != 0)
            sat.states(index) = newState; sat.indexes(index) = myIndex
            stateCount.getAndIncrement; myIndex 
          }
        } // end of synchronized
      }
    } // end of outer else
  }

  /** Add st to this. */
  def add(st: State) = getOrMaybeAdd(st.family, st.cs, st.ids, st)

  /** Iterator over the states. */
  def iterator = new Iterator[State]{
    // Index into allStates of next state. 
    private var nextIx = 1

    def hasNext = nextIx <= allStatesCount

    def next() = { val res = allStates(nextIx); nextIx += 1; res }
  }

  def size = { 
    assert(allStatesCount == stateCount.get, 
           s"${allStatesCount} ${stateCount.get}")
    stateCount.get
  } // IMPROVE
}


// =======================================================

/** A Trie, a node in the data structure used in MyTrieStateMap. */
trait Trie

/** A leaf trie, holding state st; only used at the top level for
  * states with no parameters.
  * @param ix the index in the global array where st is held.  */
case class StateTrie(st: State, ix: Int) extends Trie{
  def get = (st, ix)

  def getIndex = ix
}

/** A node of a trie, holding other tries as children. */
class MidTrie(size: Int) extends Trie{
  val tries = new Array[Trie](size)
}

/** A leaf of a trie, holding size states as children, and their indexes into
  * the global array. */
class StateArrayTrie(size: Int) extends Trie{
  val states = new Array[State](size)
  val indexes = new Array[StateIndex](size)

  def get(ix: Int): (State, StateIndex) = (states(ix), indexes(ix))

  def getIndex(ix: Int): StateIndex = indexes(ix)
}
