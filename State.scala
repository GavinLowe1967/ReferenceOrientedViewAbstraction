package ViewAbstraction

import ox.gavin.profiling.Profiler

import scala.collection.mutable.ArrayBuffer

/** States of processes. 
  * @param family the family of components that this belongs to, or -1 for a 
  * server.
  * @param cs the control state of this state.
  * @ids the identity parameters of this state.
  * @param isNew is this state being created during the compilation stage, 
  * in which case checking the type sizes are big enough is not necessary. */
class State(val family: Family, val cs: ControlState, 
            val ids: Array[Identity], isNew: Boolean = false){

  /** The component process identity. */
  def componentProcessIdentity: ComponentProcessIdentity = {
    // assert(family >= 0)
    (family, ids.head)
  }

  /** The types of parameters. */
  def typeMap: Array[Type] = State.stateTypeMap(cs)

  def processIdentities: Array[ComponentProcessIdentity] = 
    Array.tabulate(ids.length)(i => (typeMap(i), ids(i)))

  /** Check the type sizes from the script are large enough for all the
    * parameters in this State.  This is not done during compilation, because
    * typeMap is not yet initialised, and the State is bound to pass the test,
    * anyway. */
  @inline private def checkTypeSizes() = {
    val tm = typeMap
    for(i <- 0 until ids.length){
      if(ids(i) < State.SplitFreshVal && ids(i) >= typeSizes(tm(i))) 
        synchronized{
          val t = tm(i)
          println("Not enough identities of type "+typeNames(t)+" in script ("+
                    typeSizes(t)+") to represent system view\n"+toString0)
          assert(false) // sys.exit // IMPROVE
        }
    }
  }

  if(!isNew) checkTypeSizes()

  // Equality test.
  // Equality is now reference equality, as we avoid creating duplicate states.
  // @inline override def equals(that: Any) = that match{
  //   case st: State => (st eq this) || st.cs == cs && st.ids.sameElements(ids)
  // }
  // assert(-1 <= family && family < 2) 
  assert(family == -1 || ids.nonEmpty) // components have an identity

  override val hashCode = mkHash

  def id = { assert(family >= 0); ids(0) }

  /** Hash function over states. */
  @inline private def mkHash: Int = {
    var h = cs*41+family; var i = 0; var n = ids.length
    while(i < n){ h = h*41+ids(i); i += 1 }    
    h 
    // h += (h << 15) ^ 0xffffcd7d; h ^= (h >>> 10); h += (h << 3)
    // h ^= (h >>> 6); h += (h << 2) + (h << 14); h ^= (h >>> 16)
    // scala.util.hashing.byteswap32(h)
  } 

  /** Convert this to a String.  This version assumes that all the parameters
    * correspond to values in the script. */
  override def toString = {
    val paramsString = (0 until ids.length).map{ j =>
      val t = State.stateTypeMap(cs)(j); scriptNames(t)(ids(j)) }
    s"$cs[$family]"+paramsString.mkString("(", ",", ")")
  }

  /** Convert this to a String.  If this uses a parameter not in the script, it
    * is represented by its raw (type, value) representation. */
  def toString0 = {
    val paramsString = (0 until ids.length).map{ j =>
      val t = State.stateTypeMap(cs)(j)
      if(scriptNames == null) s"($t, x_${ids(j)})"
      else scriptNames(t).get(ids(j)) match{
        case Some(st) => st
        case None => s"($t, x_${ids(j)})"
      }
    }
    s"$cs[$family]"+paramsString.mkString("(", ",", ")")
  }  

  def toString00 = s"$cs[$family]"+ids.mkString("(", ",", ")")
} // End of State class

// ------------------------------------------------ Companion object

object State{
  // Following all moved to MyStateMap.scala

  // private val UseTrieStateMap = true // false // true // IMPROVE

  // /** Mapping storing all the States found so far. */
  // @volatile private var stateStore: StateMap = new InitialisationStateHashMap
  //   // if(UseTrieStateMap) new InitialisationStateHashMap else new ShardedStateMap

  // // private var renewed = false

  // /* We initially use a MyStateHashMap, but later transfer values into a
  //  * MyTrieStateMap (in renewStateStore).  This is because the latter
  //  * makes assumptions about various data structures being
  //  * initialised, but some States are created before this happens. */

  // /** The number of States stored. */
  // def stateCount = stateStore.size

  // /** Factory method to either find existing state matching (family, cs,
  //   * ids), or to create new one. 
  //   * If existing state is returned, ids is recycled. */
  // @inline 
  // def apply(family: Int, cs: ControlState, ids: Array[Identity]): State =
  //   stateStore.getOrAdd(family, cs, ids)
  //   // assert(st.family == family); if(renewed) assert(stateStore.get(ix) == st)

  // /** Factory method to either find existing state matching (family, cs,
  //   * ids), or to create new one, returning the State's index. 
  //   * If existing state is returned, ids is recycled. */
  // @inline 
  // def getByIndex(family: Int, cs: ControlState, ids: Array[Identity])
  //     : StateIndex = {
  //   val st = stateStore.getOrAddByIndex(family, cs, ids)
  //   // Note: there was a bug that made the following sometimes false.  I've
  //   // made stateStore volatile, as that might have been the issue.
  //   // 09/06/2020.
  //   assert(st != 0, 
  //          s"family = $family; cs = $cs; ids = "+ids.mkString("(", ",", ")"))
  //   st
  // }
  //   // assert(st.family == family); if(renewed) assert(stateStore.get(ix) == st)

  // /** The State with index ix. */
  // @noinline def get(ix: StateIndex): State = stateStore.get(ix)

  /** Replace the initial StateMap with a Trie-based one. */
  // def renewStateStore(numCS: Int, minCS: Int) = /* if(UseTrieStateMap) */ {
  //   print("Creating Trie-based StateMap...")
  //   // IMPROVE following if just tsm used
  //   val it = stateStore.asInstanceOf[InitialisationStateHashMap].iterator.toArray
  //   // Entry i in it will receive index i+1
  //   val tsm = new MyTrieStateMap(numCS, minCS)
  //   // var i = 1
  //   for(st <- it){ tsm.add(st); /* assert(tsm.get(i) == st, i); i += 1 */ }
  //   assert(tsm.size == stateStore.size, s"${tsm.size}; ${stateStore.size}")
  //   if(true) stateStore = tsm // IMPROVE
  //   else{
  //     val tlshm = new ThreadLocalStateHashMap(tsm)
  //     for(i <- 0 until it.length) tlshm.add(it(i), i+1)
  //     stateStore = new ThreadLocalStateHashMaps(tlshm, tsm)
  //   }
  //   println(".  Done.")
  // }

  /** Ordering over states. */
  implicit object StateOrdering extends Ordering[State]{
    /** Ordering on states. */
    def compare(st1: State, st2: State) = {
      if(st1.cs != st2.cs) st1.cs - st2.cs
      else{
        var i = 0; var n = st1.ids.length // assert(st2.ids.length == n)
        while(i < n && st1.ids(i) == st2.ids(i)) i += 1
        if(i == n) 0 else st1.ids(i) - st2.ids(i)
      }
    }
  }

  // ----- Memory management functions


  /** Maximum number of identities every returned. */
  private val MaxIds = 8

  private type IdArray = Array[Identity]

  /** Maximum number of IdArrays of each size to store. */
  private val PoolSize = 40

  /** Pool for IdArrays of size size. */
  private class IdentityArrayPool(size: Int){
    private var buff = new Array[IdArray](PoolSize)
    private var count = 0
    /* buff[0..count) stores IdArrays for re-use. */

    //var fails = 0

    /** Add ids to this pool. */
    @inline def add(ids: IdArray) =
      if(count < PoolSize){ buff(count) = ids; count += 1 }
      // else{ Profiler.count("IdArray pool add fail "+size) 
      //   //fails += 1; if(fails%1000 == 0) print("X")
      // }

    /** Get an IdArray, either from the pool or a new one. */
    @inline def get: IdArray = 
      if(count > 0){ count -= 1; buff(count) }
      else new IdArray(size) 
        // Profiler.count("IdArray pool get fail "+size)
        
  }

  /** Pool for IdArrays of size 0. */
  private object IdentityArrayPool0 extends IdentityArrayPool(0){
    // We always give the following IdArray.
    private val theIdArray = new IdArray(0)

    @inline override def add(ids: IdArray) = {}

    @inline override def get: IdArray = theIdArray
  }

  /** Supply of Array[Identity]s, to prevent GC churning.  
    * Entry len contains a supply of Array[Identity]s of length len.  */
  private object ThreadLocalIdentityArraySupply
      extends ThreadLocal[Array[IdentityArrayPool]]{
    // Initialise to size MaxIds+1, as this is normally enough.  FIXME
    override def initialValue() =
      Array.tabulate(MaxIds+1)(size => 
        if(size == 0) IdentityArrayPool0 else new IdentityArrayPool(size))
  }

  /** Get an Array[Identity] of size len, reusing a previous one if possible. */
  @inline def getIdentityArray(len: Int): Array[Identity] = /*if(false)*/{
    val pools = ThreadLocalIdentityArraySupply.get; pools(len).get
  }

  /** Return ids for recycling. */
  @inline def returnIdentityArray(ids: Array[Identity]) = /*if(false)*/{
    val pools = ThreadLocalIdentityArraySupply.get; pools(ids.length).add(ids)
  }

  // ----- Variables and functions concerning states. 

  /** Minimum value that new identities are mapped to, when splitting
    * views in Remapper.remapSplitCanonical. */
  val SplitFreshVal = 1 << 30

  /** Array storing information about types of parameters.
    * stateTypeMapArray(cs-minCS) stores information about the types of
    * parameters for control state cs.  */
  private var stateTypeMapArray: Array[Array[Type]] = null

  /** Displacement within stateTypeMapArray. */
  var minCS = Int.MaxValue

  /** Number of control states. */
  var numCS = -1

  /** Array giving the maximum number of parameters of any type in a state. */
  var maxParamsOfType: Array[Int] = null

  /** Array giving the type of the identity for control states.
    * idTypeArray(cs-minCS) gives the type of processes with control state cs,
    * or -1 for server processes with no identity.  */
  private var idTypeArray: Array[Type] = null

  /** Initialise the stateTypeMapArray, idTypeArray and minCS.  Also
    * update the StateMap.  Called by
    * FDRTransitionMap.createStateTypeMap, called by System.init. */
  def setStateTypeMap(stma: Array[Array[Type]], minCS: Int) = {
    stateTypeMapArray = stma; this.minCS = minCS; numCS = stma.size
    // set idTypeArray; need to be careful about server states with no
    // parameters
    idTypeArray = stma.map(a => if(a != null && a.nonEmpty) a(0) else -1)
    // The filter(_ != null) is necessary, because extra control states are
    // created in FDRSession.getTypeInt, but don't have types recorded.
    maxParamsOfType = Array.tabulate(numTypes)( t =>
      stma.filter(_ != null).map(_.count(_ == t)).max )
    println("maxParamsOfType = "+maxParamsOfType.mkString(", "))


    MyStateMap.renewStateStore(stma.length, minCS)
  }

  /** Array giving the types of identities for control state cs. */
  @inline def stateTypeMap(cs: ControlState): Array[Type] =
    stateTypeMapArray(cs-minCS)

  /** Type of the identity of component with control state cs. */
  private def idType(cs: ControlState): Type = idTypeArray(cs-minCS)

  /** The script name for pid. */
  def showProcessId(pid: ComponentProcessIdentity) = {
    val (t,id) = pid; scriptNames(t)(id)
  }
}
