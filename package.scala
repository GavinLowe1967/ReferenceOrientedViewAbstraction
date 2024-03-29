import scala.collection.mutable.Map
import ox.gavin.profiling.Profiler

/** The package object defines various types, so as to make them globally
  * visible. */
package object ViewAbstraction{
  // ------------------- Types, and basic operations.

  /** Identities of replicated processes. */
  type Identity = Int

  /** Is id a distinguished parameter?
    * This corresponds to it being negative. */
  @inline def isDistinguished(id: Identity): Boolean = id < 0

  /** Identifiers for types, used within parameters of processes. */
  type Type = Int 

  /** A parameter of a process. */
  type Parameter = (Type, Identity)

  /** The family of components that a process comes from, or -1 for a
    * server. */
  type Family = Int

  /** The identity of a process, typically a component, comprising its family
    * and identity. */
  type ProcessIdentity = (Family, Identity)

  /** Log of the maximum number of types. */ 
  val LogMaxNumTypes = 4

  /** The maximum number of types. */
  private val MaxNumTypes = 1 << LogMaxNumTypes

  // Note: Each type must have at most MaxTypeSize values, so is expressible
  // in 7 bits.

  /** Shift used in processIdentityToShort. */
  val ProcessIdentityShift = 7

  /** Bit mask used in shortToProcessIdentity, to extract the bits used for the
    * Identity. */
  private val ProcessIdentityMask = (1 << ProcessIdentityShift) - 1

  /** Compress a ProcessIdentity into a single Short.  We use the
    * ProcessIdentityShift least significant bits for id, the next
    * LogMaxNumTypes for t, and don't use the sign bit.*/
  @inline def processIdentityToShort(t: Type, id: Identity): Short =
    ((t << ProcessIdentityShift) + id).toShort

  @inline def processIdentityToShort(pid: ProcessIdentity): Short =
    processIdentityToShort(pid._1, pid._2)

  @inline def shortToProcessIdentity(s: Short): ProcessIdentity = 
    (s >> ProcessIdentityShift, s & ProcessIdentityMask)

  def check(t: Type, id: Int) = 
    assert(shortToProcessIdentity(processIdentityToShort(t,id)) == (t,id),
      s"t = $t, id = $id, result = "+
        shortToProcessIdentity(processIdentityToShort(t,id)))
  check(0,0); check(2,5); check(MaxNumTypes-1, 3); 
  check(MaxNumTypes-1, ProcessIdentityMask)

  /** Control states of processes (which include all data other than
    * Identitys). */
  type ControlState = Int

  /** Index into the global array of States in the State object. */
  type StateIndex = Int

  /** Representation of events. */
  type EventInt = Int

  /** Sentinel uses at end of lists of events, as part of the representation of
    * transitions. */
  val Sentinel = Int.MaxValue

  /** The representation of tau. */
  val Tau: EventInt = 1

  /** The type of maps recording the values that parameters get remapped to.  
    * map(t)(arg) records the value that arg of type t gets remapped to,
    * or -1 if no value has been allocated yet.  I.e., it represents the
    * mapping
    *  {(t,arg) -> (t, map(t)(arg)) |
    *       0 <= t < numTypes, 0 <= arg < size(t), map(t)(arg) != -1}.
    */
  type RemappingMap = Array[Array[Identity]]

  /** The type of maps giving the next argument to map a parameter of
    * type t.  The corresponding RemappingMap has domain all
    * parameters (t,i) for i <- [0..nextArg(t)), for each t. */
  type NextArgMap = Array[Int]

  /** A list, for each type, of non-fresh values that a particular parameter can
    * be mapped to. */
  type OtherArgMap = Array[List[Identity]]

  // ------- bitmaps over parameters

  type BitMap = Array[Array[Boolean]]

// FIXME: the size of each row is a hack, and may be insufficient 
  @inline def newBitMap: BitMap = {
    Profiler.count("newBitMap") // 707M with lazySetNoJoined
    val newIds = new BitMap(numTypes); var f = 0
    while(f < numTypes){ newIds(f) = new Array[Boolean](typeSizes(f)+1); f += 1 }
    newIds
  }

  // --------------------------- Various useful functions

  /** Append two lists together: more efficient than API version. */
  def append(xs: List[Int], ys: List[Int]): List[Int] =
    if(xs.isEmpty) ys else xs.head :: append(xs.tail, ys)

  /** Append two lists together: more efficient than API version. */
  def append1[A](xs: List[A], ys: List[A]): List[A] =
    if(xs.isEmpty) ys else xs.head :: append1(xs.tail, ys)

  /** Does xs contain x? */
  @inline def contains[A](xs: Array[A], x: A): Boolean = {
    var i = 0
    while(i < xs.length && xs(i) != x) i += 1
    i < xs.length
  }

  def contains[A](xs: List[A], x: A): Boolean = 
    xs.nonEmpty && (xs.head == x || contains(xs.tail, x))


  /** Flatten (concat) a list of lists: more efficient than API version. */
  def flatten(xss: List[List[Int]]): List[Int] =
    if(xss.isEmpty) List[Int]()
    else append(xss.head, flatten(xss.tail))

  /** Flatten (concat) an array of lists: more efficient than API version. */
  def flatten(xss: Array[List[Int]]): List[Int] = {
    // Optimise for common cases.
    val size = xss.length
    if(size == 1) xss(0)
    else if(size == 2) append(xss(0), xss(1))
    else{
      var ys = xss(size-1); var i = size-2
      while(i >= 0){ ys = append(xss(i), ys); i -= 1 }
      ys
    }
  }

  /** Is n a power of 2? */
  def checkPow2(n: Int) = {
    var k = n
    while(k > 1){
      assert((k&1) == 0, "MyHashSet: initial size not a power of 2")
      k = k >>> 1
    }
  }

  /** The smallest power of 2 at least n. */
  def powerOfTwoAtLeast(n: Int): Int = {
    var p = 1
    while(p < n) p *= 2
    p
  }

  /** Improved hash of x; guaranteed not to be 0. */
  @inline def hashOf[A](x: A): Int = {
    val h = scala.util.hashing.byteswap32(x.hashCode)
    // var h = x.hashCode
    // h ^= ((h >>> 20) ^ (h >>> 12))
    // h ^= (h >>> 7) ^ (h >>> 4)
    if(h == 0) 12344577 else h
  }

  /** Comparison of hash values. */
  @inline def compareHash(h1: Int, h2: Int) = {
    if(h1 < h2) -1 else if(h1 == h2) 0 else 1
  }

  private val formatter = java.text.NumberFormat.getNumberInstance

  /** Print an Int with commas. */
  def printInt(n: Int): String = formatter.format(n)

  def printLong(n: Long): String = formatter.format(n)

  // ------------------------------------------- Global variables

  /** Are we currently compiling?  This is used to control checks when a new
    * State is created. */
  var compiling = true

  /** Current ply of the search. */
  var ply = 1

  /** Are we running in verbose mode, giving more output? */
  var verbose = false

  /** Should the final ViewSet be printed? */
  var showViews = false

  /** Should the new views on each ply be shown? */
  var showEachPly = false

  /** Should each transition be shown? */
  var showTransitions = false

  /** Should information about redundancies be shown in
    * EffectOn.processInducedInfo? */
  var showRedundancies = false

  /** Should we use the new version of effectOn unification with singleRef, as
    * in SingleRefEffectOnUnification.scala? */
  val newEffectOn = true

  var NewEffectOnStore3 = false

  /** Switch to activate various assertions. */
  val debugging = true // false

  /** Are we creating Views with just a single referenced component? */
  var singleRef = false

  /** Do we create TwoStepMissingCommon objects? */
  var useTwoStepMC = false

  /** Are we supporting debugging? */ 
  var debuggable = true

  /** Do we do the sanity check on EffectOnStore? */
  var doSanityCheck = false

  /** Do we use NewViewSet? */
  val UseNewViewSet = true

  /** Do we report the size of the EffectOnStore? */
  var reportEffectOn = false

  /** Are we using NewEffectOnStore? */
  val useNewEffectOnStore = true

  /** Are we using NewEffectOnStore "lazily", initially working with partial
    * maps, and extending to full maps only if/when all cross reference views
    * are found? */
  //var lazyNewEffectOnStore =  false

  /** Do we use the new way of calculating reference views in
    * TransitionTemplateExtender.extendTransitionTemplateBy? */
  var useNewReferencingViews = true 

  /** Should we intermittently do explicit garbage collections? */
  var doGC = false

  /** In Checker.endOfPly, do we swap the order of the "views" and "transitions
    * stages?   Used in debugging, 2022/08/29. */
  // var swappedEndOfPly = false

  /** Are we using the optimisation with
    * ComponentView0.doneInducedPostServersRemaps?  This seems to give a
    * marginal advantage. */
  val StoreDoneInducedPostServersRemaps = true

  /** With singleRef, in SingleRefEffectOnUnification, do we detect a repeat of
    * a result-defining map with the same post.servers, *and* allowing
    * unifications?  This seems to give a marginal advantage. */
  val DetectRepeatRDMapWithUnification = false

  // IMPROVE: move
  /** The number of indexing types in the current system. */
  var numTypes = -1

  /** The number of families of replicated components. */
  var numFamilies = -1

  /** The type identifiers of the indexing types, by component family.
    * Set by Components. */
  var indexingTypes: Array[Int] = null

  /** The sizes of the indexing subtypes (i.e. ignoring distinguished
    * values), indexed by type identifier. */
  var typeSizes : Array[Int] = null

  /** The sizes of the supertypes (i.e. including distinguished values). */
  var superTypeSizes: Array[Int] = null

  /** The number of distinguished values of each type. */
  var distinguishedSizes: Array[Int] = null

  /** The number of non-distinguished values of each type that we might need to
    * deal with in remappings. */
  var remapSizes: Array[Int] = null

  /** The maximum allowed size of any type.  Required for Remapper.summarise. */
  val MaxTypeSize = (1<<7)-2

  /** Set numTypes to be nt, and numFamilies to be nf; initialise arrays
    * indexed by types. */
  def setNumTypes(nt: Int, nf: Int) = {
    println("numTypes = "+nt+"; numFamilies = "+nf)
    require(nt < MaxNumTypes, s"Too many types: maximum $MaxNumTypes allowed.")
    numTypes = nt; numFamilies = nf
    typeSizes = new Array[Int](nt)
    superTypeSizes = new Array[Int](nt)
    distinguishedSizes = new Array[Int](nt)
  }

  /** The names of the types.  Indexed by component family number.  Set
    * by System. */
  var familyTypeNames: Array[String] = null

  /** The names of the families.  Set by System. */
  var familyNames: Array[String] = null

  /** The names of the types, indexed by type identifier.  Set by Components. */
  var typeNames: Array[String] = null

  /** The number of visible events.  Standard visible events are numbered
    * [3..numEvents+3). */
  // var numEvents = -1

  /** The size to initialise arrays of events.  Normal events are numbered in
    * [3..eventsSize).  Set in System.scala. */
  var eventsSize = -1

  /** The maximum size of any subtype. */
  var maxSubtypeSize = -1

  /** The script names for parameters. */
  var scriptNames: Map[Type, Map[Identity, String]] = null

  /** The number of component control states.  Set by constructor of System.
    * Component control states will be in the range
    * [0..numCptControlStates). */
  var numCptControlStates = -1

  /** Number of machine threads. */
  // var numThreads = Runtime.getRuntime.availableProcessors 

  /** Number of threads used during checking. */
  var numWorkers = Runtime.getRuntime.availableProcessors 

  trait EventPrinter{
    def eventToString(e: Int): String
  }

  /** Object that can give script name of events.  Instantiated by fdrSession by
    * System. */
  var eventPrinter: EventPrinter = null

  /** Show the script name corresponding to event e. */
  def showEvent(e: Int) = eventPrinter.eventToString(e)

}
