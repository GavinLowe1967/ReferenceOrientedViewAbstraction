package ViewAbstraction
import collection.{MyHashMap,MyLockFreeReadHashMap}

// import ox.cads.util.Profiler
import scala.collection.mutable.{Map,Set,ArrayBuffer}
import scala.math.Ordering.Implicits._
 
/** A model of the servers.
  * @param file the object which parses the file.
  * @param fdrSession the session with FDR.
  * @param transMapBuilder the object that builds transition maps.
  * @param componentEventMap an array, indexed by events, giving the component 
  * process identities of components that synchronise on each event.
  * @param idSizes array giving the number elements of each distinguished
  * subtype. */
class Servers(
  file: CSPFileParser, fdrSession: FDRSession, fdrEvents: FDREvents,
  transMapBuilder: FDRTransitionMap, componentEventMap: Array[List[Parameter]],
  idSizes: Array[Int]
){

  assert(idSizes.length == numFamilies, s"${idSizes.length}; $numFamilies")

  /** Are the servers defined using renaming? */
  private val usesRenaming = file.serversRenameName.nonEmpty

  /** Number of servers. */
  private val numServers =
    fdrSession.eval(
      "length("+
        (if(usesRenaming) file.serversRenameName else file.serversName)+
        ")"
    ).toInt

  /** A list giving the states of all the servers. */
  type StateVector = List[State]

  /** transMaps(i)(st) gives a pair (es, postss) such that for each j, server i
    * has a transition from state st under event es(j) to each state in
    * postss(j).  */
  private val transMaps =
    new Array[Map[State, (Array[EventInt], Array[StateVector])]](numServers)
  /* Note, transMaps is created during initialisation, and subsequently
   * only read, so doesn't need to be protected. */

  /** List of initial states for these servers.
    * set in init() */
  var inits: StateVector = null

  /** Bit map showing which events are in the alphabet of any server (used in
    * System.scala).  Set in init. */
  var alphaBitMap: Array[Boolean] = null

  /** Map that gives, for each event e, the indices of servers that synchronise
    * on e.  Set in init.  */
  private var eventMap: Array[Array[Int]] = null

  // private def showEvent(e: EventInt) = fdrSession.eventToString(e)

  /** List of server names. */
  val serverNames = new Array[String](numServers)

  /** Bitmap indicating which servers are active. */
  private val activeServer = new Array[Boolean](numServers)

  /** Bitmaps indicating which events are events of an active server. */
  private val activeServerEvent = new Array[Boolean](eventsSize)

  def isActiveServerEvent(e: EventInt) = activeServerEvent(e)

  /** Maximum event number synchronised on with a component. */
  val maxComponentEvent = componentEventMap.length-1

  /** String giving i'th entry in the servers set. */
  private def entry(i: Int) =
    if(usesRenaming) s"nth_(${file.serversRenameName}, $i)"
    else s"nth_(${file.serversName}, $i)"

  /** The alphabets of the servers.  Initialised in initAlphas. */
  private val alphas: Array[Set[EventInt]] = Array.fill(numServers)(Set[Int]())

  // private def getAlphabet(e: String) = println(fdrSession.eval(e))

  private def initAlphas() = {
    // Build alphabet for each server
    print("Creating alphabets")
    for(i <- 0 until numServers){
      print(s"Building alphabet for server $i: ${serverNames(i)}...")
      val term = 
        if(usesRenaming) s"third4_(${entry(i)})" else s"second3_(${entry(i)})"
      // getAlphabet(term)
      val alpha = fdrSession.evalSeqSeqOrSeq(term, st => st)
      for(st <- alpha) alphas(i) += fdrEvents.eventToInt(st)
      println()
    }
    println()
    // Build map (as array) from events to the list of synchronising servers.
    eventMap = Array.tabulate(eventsSize)( // (maxEvent+1)( 
      e => (0 until numServers).filter(alphas(_).contains(e)).toArray)
    // Build bitmap showing which events are in alphabet of any server
    alphaBitMap = new Array[Boolean](eventsSize)
    for(i <- 0 until numServers; e <- alphas(i)){
      alphaBitMap(e) = true
      if(activeServer(i)) activeServerEvent(e) = true
    }
  }

  /** Build transition system for servers. */
  private def init() = {
    println("Creating servers")
    for(i <- 0 until numServers){
      serverNames(i) = fdrSession.eval(
        if(usesRenaming) s"first4_(${entry(i)})" else s"first3_(${entry(i)})" ) 
      val activeString = fdrSession.eval(
        if(usesRenaming) s"fourth4_(${entry(i)})" else s"third3_(${entry(i)})")
      assert(activeString == "true" || activeString == "false")
      activeServer(i) = activeString == "true"
      println(serverNames(i)+": "+(if(activeServer(i)) "active" else "passive"))
    }
    // Build alphabet for each server
    initAlphas()
    // Build transitions
    val initStates: Array[State] = new Array[State](numServers)
    for(i <- 0 until numServers){
      val sName = serverNames(i)
      print(s"Building server transitions for server $i: $sName")
      val oRenamingString = 
        if(usesRenaming) Some(s"second4_(${entry(i)})") else None
      val (init, map) = 
        transMapBuilder.buildTransMap(sName, alphas(i), -1, oRenamingString)
      initStates(i) = init; transMaps(i) = map
    }
    inits = initStates.toList
  }

  init()

  // --------- Representation of transitions

  /** Representation of transitions from a StateVector as parallel arrays of
    * events (sorted, with a sentinel) and lists of next states. */
  type Trans = (ArrayBuffer[EventInt], ArrayBuffer[List[StateVector]])

  class ServerTransitions{
    /** Events involving no synchronisation with a component. */
    val eventsSolo = new ArrayBuffer[EventInt]
    val nextsSolo = new ArrayBuffer[List[StateVector]]

    override def toString = "ServerTransitions: "+eventsSolo.mkString(", ")

    /** Transitions involving synchronisation with one component.
      * transSync(f)(i) represents transitions synchronised with the
      * component with process identity (f,i); except null is used to
      * repsesent no transitions (for compactness).  */
    val transSync = Array.tabulate(numFamilies)(f =>
      Array.fill(idSizes(f))(
        (new ArrayBuffer[EventInt], new ArrayBuffer[List[StateVector]])
      ) )

    /** Transitions synchronising with two components.  For p1 < p2,
      * transSync2Map(p1,p2) gives the synchronisations with p1 and
      * p2, or is empty if there are no such.  */
    private val transSync2Map = 
      Map[(ProcessIdentity, ProcessIdentity), Trans]()

    /** Get transitions synchronising with p1 and p2, initialising if
      * needs be. */
    def getOrInitSync2
      (p1: ProcessIdentity, p2: ProcessIdentity): Trans = {
      assert(p1 != p2)
      transSync2Map.getOrElseUpdate(
        (p1 min p2, p1 max p2),
        (new ArrayBuffer[EventInt], new ArrayBuffer[List[StateVector]]))
    }

    /** Get transitions synchronising with p1 and p2. */
    def transSync2(p1: ProcessIdentity, p2: ProcessIdentity)
        : Trans =
      transSync2Map.getOrElse((p1 min p2, p1 max p2), null)

    /** Add sentinels, and replace empty sets of transitions in transSync by
      * null. */
    def finish = {
      eventsSolo += Int.MaxValue
      for(f <- 0 until numFamilies; i <- 0 until idSizes(f)){
        val es = transSync(f)(i)._1
        if(es.nonEmpty) es += Sentinel else transSync(f)(i) = null
      }
      for(((p1,p2),(es,_)) <- transSync2Map.iterator){ es += Sentinel }
    }
  } // end of ServerTransitions

  /** Map giving memoized representation of transitions from a particular vector
    * of states. */
  private val transStore: MyHashMap[StateVector, ServerTransitions] =
    new MyLockFreeReadHashMap[StateVector, ServerTransitions]

  def transStoreSize = transStore.size

  /** The transitions of the servers from states. */
  def transitions(states: StateVector): ServerTransitions = 
    transStore.getOrElseUpdate(states, categoriseTrans(states))

  /** Create the transitions from states. */
  private def categoriseTrans(states: StateVector): ServerTransitions = {
    assert(states.length == numServers)
    // eventsLists(i) gives the events of server i; nextLists(i) gives the
    // corresponding lists of next-states.
    val eventLists = new Array[Array[EventInt]](numServers)
    val nextLists = new Array[Array[StateVector]](numServers)
    for(i <- 0 until numServers){
      val (es, nextss) = transMaps(i)(states(i))
      eventLists(i) = es; nextLists(i) = nextss
    }
    // indices into eventLists and nextLists
    val indices = new Array[Int](numServers)
    // Build up result in following
    val serverTransitions = new ServerTransitions

    // Create tau transitions
    var tauNexts = List[StateVector]()
    for(j <- 0 until numServers){
      val e = eventLists(j)(0)
      if(e == Tau){ 
        tauNexts =
          nextLists(j)(0).map(post => states.patch(j, List(post), 1)) ++
            tauNexts
        indices(j) = 1 
      }
    }
    if(tauNexts.nonEmpty){
      serverTransitions.eventsSolo += Tau;
      serverTransitions.nextsSolo += tauNexts
    }

    // Now create non-Tau transitions
    var done = false
    // Next event of each component
    val es = Array.tabulate(numServers)(j => eventLists(j)(indices(j)))
    while(!done){
      val e = es.min // next event to consider
      if(e != Int.MaxValue){
        var serverIndices = eventMap(e) // indices of servers that synch on e
        assert(e != Tau && serverIndices.nonEmpty, fdrEvents.eventToString(e))
        // Calculate (in cptDsts) states after e, for each server in
        // serverIndices
        val cptDsts = new Array[List[State]](numServers)
        // canSync stores whether we can synchronise on this event.
        var canSync = true
        var j = 0 // j is index into serverIndices
        while(j < serverIndices.size && canSync){
          val c = serverIndices(j) // this component
          val index = indices(c) // index into eventLists(c), nextLists(c)
          if(eventLists(c)(index) == e){
            cptDsts(c) = nextLists(c)(index) // all states of c after e
            indices(c) = index+1; es(c) = eventLists(c)(index+1)
          }
          else canSync = false // This event is blocked
          j += 1
        }
        // Advance over other events if j < serverIndices.size, so !canSync
        while(j < serverIndices.size){
          val c = serverIndices(j); val index = indices(c)
          if(eventLists(c)(index) == e){
            indices(c) = index+1; es(c) = eventLists(c)(index+1)
          }
          j += 1
        }

        /* Cartesian product of cptDsts[i..numServers).  All ways of selecting
         * a state from cptDsts(j) for each j <- [i..numServers) with cptDsts(j)
         * != null, or taking states(j) when cptDsts(j) = null. */
        def cp(i: Int): List[StateVector] = {
          if(i == numServers) List(List[State]())
          else{
            val cp1 = cp(i+1)
            if(cptDsts(i) == null){ val st = states(i); cp1.map(st::_) }
            else for(dst <- cptDsts(i); dsts1 <- cp1) yield dst::dsts1
          }
        }

        // Calculate next vectors of states, and store
        if(canSync){
          val nexts = cp(0) // next vectors of states after e
          val cpts = componentEventMap(e)
          if(cpts.isEmpty){ // private event of the servers
            serverTransitions.eventsSolo += e
            serverTransitions.nextsSolo += nexts
          }
          else{ // synchronisation with one component, with identity (t,i)
            val (f,i) = cpts.head
            val (es,nextss) =
              if(cpts.length == 1) serverTransitions.transSync(f)(i)
              else serverTransitions.getOrInitSync2(cpts(0), cpts(1))
            es += e; nextss += nexts
          }
        } // end of if(canSync)
      } // end of if(e != Int.MaxValue)
      else done = true
    } // end of while(!done)

    serverTransitions.finish
    serverTransitions
  }
}
