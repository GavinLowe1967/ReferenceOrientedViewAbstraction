package ViewAbstraction

import ox.gavin.profiling.Profiler

import scala.collection.mutable.ArrayBuffer

class InsufficientIdentitiesException extends Exception

/** States of processes. 
  * @param family the family of components that this belongs to, or -1 for a 
  * server.
  * @param cs the control state of this state.
  * @ids the identity parameters of this state.
  * @param isNew is this state being created during the compilation stage, 
  * in which case checking the type sizes are big enough is not necessary. 
  */
class State(val family: Family, val cs: ControlState, 
            val ids: Array[Identity], isNew: Boolean = false){
  /** The number of parameters of this. */
  def length = ids.length

  /** The component process identity. */
  val componentProcessIdentity: ProcessIdentity = {
    if(family >= 0) (family, ids(0)) else null
  }

  /** Does this have a process identity matching (f,id)? */
  @inline def hasPID(f: Family, id: Identity) = f == family && id == ids(0)

  /** Does this have a process identity matching pid? */
  @inline def hasPID(pid: ProcessIdentity) = pid._1 == family && pid._2 == ids(0)

  /** The types of parameters. */
  @inline def typeMap: Array[Type] = State.stateTypeMap(cs)
  // Note: can't be set at the point of object creation.

  def processIdentity(i: Int): ProcessIdentity = (typeMap(i), ids(i))

  /** The process identities corresponding to ids. */
  private var pIds: Array[ProcessIdentity] = null

  def processIdentities: Array[ProcessIdentity] = {
    if(pIds == null) pIds = Array.tabulate(ids.length)(i => (typeMap(i), ids(i)))
    pIds
  }

  /** Bitmap giving the parameters of this. */
  private var paramsBitMap: BitMap = null

  /** Initialise paramsBitMap.  Needs typeMap to be initialised. */
  @inline private def initParamsBitMap = 
    if(paramsBitMap == null){
      paramsBitMap = newBitMap; var i = 0
      while(i < length){
        val id = ids(i)
        if(!isDistinguished(id)) paramsBitMap(typeMap(i))(id) = true
        i += 1
      }
    }

  /** Does this have a reference to (t,id)?  Pre: this is not its identity. */
  @inline def hasRef(t: Family, id: Identity) = {
    initParamsBitMap // make sure initialised
    assert(!hasPID(t,id)); paramsBitMap(t)(id)
  }

  /** Does this have a parameter (t,id)? */
  @inline def hasParam(t: Family, id: Identity): Boolean = {
    initParamsBitMap; paramsBitMap(t)(id)
    // var i = 0
    // while(i < length && (typeMap(i) != t || ids(i) != id)) i += 1
    // i < length
  }

  /** Information about which references are used to create views.  It is set
    * the first time includeParam is called (it can't be done before
    * compilation is complete).  Subsequently, a value of null indicates that
    * all references can be used to create views. */
  private var includeInfo: Array[Boolean] = null

  /** Has includeInfo been set? */
  private var includeInfoSet = false

  /** Should the ith parameter of this be used for creating views? */
  @inline def includeParam(i: Int) = {
    // IMPROVE: cache includeInfo in this object.  This can't be done during
    // compilation, however.
    if(!includeInfoSet){ 
      includeInfo = State.getIncludeInfo(cs); includeInfoSet = true 
    }
    includeInfo == null || includeInfo(i)
  }

  /** Bit map giving parameters for which corresponding states are included in
    * views. */
  private var includedParamBitMap: Array[Array[Boolean]] = null

  /** Does this state have a parameter (f,id) that is not an omitted
    * reference?  */
  def hasIncludedParam(f: Family, id: Identity) = {
    if(includedParamBitMap == null){ 
      includedParamBitMap =
        // FIXME: the +2 is a hack
        Array.tabulate(numTypes)(t => new Array[Boolean](2*typeSizes(t)))
      for(i <- 0 until length)
        if(!isDistinguished(ids(i)) && includeParam(i)) 
          includedParamBitMap(typeMap(i))(ids(i)) = true
    }
    includedParamBitMap(f)(id)
  }

  /** A bound on the values of each type. */
  private var paramsBound: Array[Int] = null 

  /** A bound on the values of each type. */
  def getParamsBound: Array[Int] = {
    if(paramsBound == null){
      paramsBound = new Array[Int](numTypes); var i = 0
      while(i < length){
        val id = ids(i); val t = typeMap(i); i += 1
        paramsBound(t) = paramsBound(t) max (id+1)
      }
    }
    paramsBound
  }

  /** Check the type sizes from the script are large enough for all the
    * parameters in this State.  This is not done during compilation, because
    * typeMap is not yet initialised, and the State is bound to pass the test,
    * anyway. */
  @inline private def checkTypeSizes() = {
    val tm = typeMap
    for(i <- 0 until ids.length){
      if(ids(i) >= typeSizes(tm(i))) 
        synchronized{
          val t = tm(i)
          println("Not enough identities of type "+typeNames(t)+" in script ("+
                    typeSizes(t)+") to represent system view\n"+toString0)
          throw new InsufficientIdentitiesException 
        }
    }
  }

  /** Is this State representable using the values defined in the input
    * script?  I.e. is every identity less than the size of the corresponding
    * type? */
  val representableInScript = 
    isNew || (0 until ids.length).forall(i => ids(i) < typeSizes(typeMap(i)))

  /** Add each identity (f,id) of this, from index `from` upwards, that is not
    * an identity of serversIds to bitmap. */
  def addIdsToBitMap(
    bitmap: Array[Array[Boolean]], serverIds: Array[Array[Boolean]], 
    from: Int = 0)
  = {
    var j = from
    while(j < ids.length){
      val f = typeMap(j); val id = ids(j); j += 1
      assert(id < bitmap(f).length && id < serverIds(f).length)
      if(!isDistinguished(id) && !serverIds(f)(id)) bitmap(f)(id) = true
    }
  }


  // Note: Equality is reference equality, as we avoid creating duplicate
  // states.

  assert(family == -1 || ids.nonEmpty) // components have an identity

  override val hashCode = mkHash

  def id = { assert(family >= 0); ids(0) }

  /** Index of (f,id) in the references of this, or length if it doesn't
    * appear. */
  def indexOf(f: Family, id: Identity): Int = {
    var j = 0
    while(j < length && (typeMap(j) != f || ids(j) != id)) j += 1
    j
  }

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
    cs.toString+paramsString.mkString("(", ",", ")") // [$family]
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
    s"$cs"+paramsString.mkString("(", ",", ")") // [$family]
  }  

  def toString00 = s"$cs"+ids.mkString("(", ",", ")") // [$family]

  /** Ordering on ServerStates values.  Return a value x s.t.: x < 0 if this <
    * that; x == 0 when this == that; x > 0 when this > that. */
  def compare(that: State) = {
    if(this == that) 0
    else{
      val hashComp = compareHash(hashCode, that.hashCode)
      if(hashComp != 0) hashComp
      else{
        val stateDiff = cs - that.cs // both are non-negative, so this is sound
        if(stateDiff != 0) stateDiff
        else{
          assert(family == that.family); var i = 0
          // They must have a different id
          while(ids(i) != that.ids(i)) i += 1
          ids(i) - that.ids(i) // both non-negative
        }
      }
    }
  }

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
  // val SplitFreshVal = 1 << 30

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

  /** Max number of values of each type that we need to keep track of in any
    * remapping. */
  //var rowSizes: Array[Int] = null

  /** Array giving the type of the identity for control states.
    * idTypeArray(cs-minCS) gives the type of processes with control state cs,
    * or -1 for server processes with no identity.  */
  private var idTypeArray: Array[Type] = null

  /** Array to hold information about which referenced components should be
    * included in Views.  Created in setStateTypeMap.  Updated and read via
    * setIncludeInfo and getIncludeInfo.  Values are stored with an offset of
    * minCS.  Null entries mean to include all components. */
  private var includeInformation: Array[Array[Boolean]] = null

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
    includeInformation = new Array[Array[Boolean]](State.numCS)
    //rowSizes = Array.tabulate(numTypes)( t => typeSizes(t) /* + maxParamsOfType(t) */ )
    // MyStateMap.renewStateStore(stma.length, minCS)
  }

  /** Array giving the types of identities for control state cs. */
  @inline def stateTypeMap(cs: ControlState): Array[Type] =
    stateTypeMapArray(cs-minCS)

  /** Is cs a reachable control state? */
  def isReachable(cs: ControlState) =
    0 <= cs && cs-minCS < stateTypeMapArray.length

  /** Type of the identity of component with control state cs. */
  private def idType(cs: ControlState): Type = idTypeArray(cs-minCS)

  def setIncludeInfo(cs: ControlState, includeInfo: Array[Boolean]) =
    includeInformation(cs-minCS) = includeInfo

  /** Get the include information for cs. */
  @inline def getIncludeInfo(cs: ControlState) = includeInformation(cs-minCS)

  /** Should the i'th references component from cs be included in views? */
  @inline def shouldInclude(cs: ControlState, i: Int) = {
    val includeInfo = getIncludeInfo(cs)
    includeInfo == null || includeInfo(i)
  }

  /** The script name for pid. */
  def showProcessId(pid: ProcessIdentity) = {
    val (t,id) = pid; scriptNames(t)(id)
  }

  /** A template used in indexMap. */
  // private var indexMapTemplate: Array[Array[Int]] = null

  /** Reset for a new check */
  def reset = {} // indexMapTemplate = null

  /** A map, implemented as an array, giving the index of identities within
    * states, or -1 if an index does not appear. */ 
/*
  @inline def indexMap(states: Array[State]): Array[Array[Int]] = {
    if(indexMapTemplate == null) 
      indexMapTemplate =
        Array.tabulate(numTypes)(f => Array.fill(typeSizes(f)+1)(-1))
// FIXME: the +1 is a bit arbitrary
    // Clone indexMaptemplate
    val map = new Array[Array[Int]](numTypes); var f = 0
    while(f < numTypes){ map(f) = indexMapTemplate(f).clone; f += 1 }
    // Now update based on states
    var i = 0
    while(i < states.length){
      val st = states(i); map(st.family)(st.ids(0)) = i; i += 1
    }
    map
  }
 */

}
