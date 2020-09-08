package ViewAbstraction

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
  file: CSPFileParser, fdrSession: FDRSession,
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
    * System.scala). */
  var alphaBitMap: Array[Boolean] = null

  /** Map that gives, for each event e, the indices of servers that synchronise
    * on e. */
  private var eventMap: Array[Array[Int]] = null

  private def showEvent(e: EventInt) = fdrSession.eventToString(e)

  /** Representation of the tau event. */
  // private val Tau = 1

  /** List of server names. */
  val serverNames = new Array[String](numServers)

  /** Maximum event number synchronised on with a component. */
  val maxComponentEvent = componentEventMap.length-1

  // private val nthString = fdrSession.nthString
    // "let nth(xs_,n_) = if n_ == 0 then head(xs_) else nth(tail(xs_), n_-1) "+
    //   "within "

  /** Build transition system for servers. */
  private def init() = {
    println("Creating servers")
    // The value of ServerSet from the file
    // val pairsStrings = fdrSession.setStringToList(file.serversName)
    val indices = (0 until numServers).toList
    // Name of i-th server
    // def getServerName(i: Int) =
    //   fdrSession.eval(
    //     if(usesRenaming) s"first3_(nth_(${file.serversRenameName}, $i))"
    //     else s"first_(nth_(${file.serversName}, $i))" )
    // val sNames = Array.tabulate(numServers)(getServerName)
    for(i <- 0 until numServers) 
      serverNames(i) = fdrSession.eval(
        if(usesRenaming) s"first3_(nth_(${file.serversRenameName}, $i))"
        else s"first_(nth_(${file.serversName}, $i))" )
    // Build alphabet for each component
    print("Creating alphabets")
    val alphas: Array[Set[EventInt]] = Array.fill(numServers)(Set[Int]())
    for(i <- indices){
      print(s"Building alphabet for server $i: ${serverNames(i)}...")
      val alpha = fdrSession.evalSeqSeqOrSeq( 
        if(usesRenaming) s"third3_(nth_(${file.serversRenameName}, $i))"
        else s"second_(nth_(${file.serversName}, $i))",
        st => st)
      for(st <- alpha) alphas(i) += fdrSession.eventToInt(st)
      println
    }
    println
    val maxEvent = alphas.map(_.max).max // IMPROVE: use eventsSize?
    // Build map (as array) from events to the list of synchronising servers.
    eventMap = Array.tabulate(maxEvent+1)( 
      e => indices.filter(alphas(_).contains(e)).toArray)
    // Build bitmap showing which events are in alphabet of any server
    alphaBitMap = new Array[Boolean](eventsSize)
    for(alpha <- alphas; e <- alpha) alphaBitMap(e) = true

    // Build transitions
    val initStates: Array[State] = new Array[State](numServers)
    for(i <- indices){
      val sName = serverNames(i)
      // fdrSession.eval(
        // if(usesRenaming) s"first3_(nth_(${file.serversRenameName}, $i))"
        // else s"first_(nth_(${file.serversName}, $i))" )
      print(s"Building serverTransMap for server $i: $sName")
      // serverNames(i) = sName
      val oRenamingString = 
        if(usesRenaming) Some(s"second3_(nth_(${file.serversRenameName}, $i))")
        else None
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
      Map[(ComponentProcessIdentity, ComponentProcessIdentity), Trans]()

    /** Get transitions synchronising with p1 and p2, initialising if
      * needs be. */
    def getOrInitSync2
      (p1: ComponentProcessIdentity, p2: ComponentProcessIdentity): Trans = {
      assert(p1 != p2)
      transSync2Map.getOrElseUpdate(
        (p1 min p2, p1 max p2),
        (new ArrayBuffer[EventInt], new ArrayBuffer[List[StateVector]]))
    }

    /** Get transitions synchronising with p1 and p2. */
    def transSync2(p1: ComponentProcessIdentity, p2: ComponentProcessIdentity)
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
      for(((p1,p2),(es,_)) <- transSync2Map.iterator){
        // println("Three-way synchronisations involving "+p1+" and "+p2+
        //           ": "+es.length)
        es += Sentinel
      }
    }
  } // end of ServerTransitions

  /** Map giving memoized representation of transitions from a particular vector
    * of states. */
  private val transStore: MyHashMap[StateVector, ServerTransitions] =
    new MyLockFreeReadHashMap[StateVector, ServerTransitions]
    // new SimpleHashMap[StateVector, ServerTransitions]
    // new ShardedHashMap[StateVector, ServerTransitions](128, 4)
  // Map[StateVector, ServerTransitions]()
  /* All accesses to transStore should be protected by a synchronized
   * block. */

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
        assert(e != Tau && serverIndices.nonEmpty, fdrSession.eventToString(e))
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
            // if(cpts.length == 2)
            //   println("Three-way synchronisation on "+showEvent(e))
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
