package ViewAbstraction

import scala.collection.JavaConverters._
import scala.collection.mutable.{Map,Set,ArrayBuffer}

/** Model of the replicated components, possibly comprising multiple families
  * of processes.
  * 
  * @param processNames the process name (from the script) for each type of 
  * component process.
  * @param fdrTypeIds the representation of each type inside FDR. 
  * @param alphaNames the name of the alphabet for each type components process.
  */
class Components(
  fdrSession: FDRSession, fdrEvents: FDREvents, 
  transMapBuilder: FDRTransitionMap,
  fdrTypeIds: Array[Long], processNames: Array[String], 
  alphaNames: Array[String], renames: Array[Option[String]], 
  actives: Array[Boolean]
){
  println(
    "fdrTypeIds = "+fdrTypeIds.mkString(",")+
      "\nprocessNames = "+processNames.mkString(",")+
      "\nalphaNames = "+alphaNames.mkString(",")+
      "\ncomponentActives = "+actives.mkString(",")
  )

  // Check lengths agree
  assert(fdrTypeIds.length == numFamilies &&  
           processNames.length == numFamilies &&
           alphaNames.length == numFamilies &&
           renames.length == numFamilies && actives.length == numFamilies)

  /** list of identities, for each process type. */
  private val idTypes: Array[Array[String]] =
    familyTypeNames.map(fdrSession.getTypeValues(_).toArray)
  assert(idTypes.length == numFamilies)

  /** Number of distinct identities in the script for each indexing type
    * (i.e. excluding distinguished values), indexed by family numbers. */
  private val idSizes: Array[Int] = idTypes.map(_.length)
  // Note: the above ends up holding the same values as typeSizes, but
  // the latter is not yet set.

  /** Identities of components for each process type. */
  private val indices: Array[List[Identity]] =
    idSizes.map(idSize => (0 until idSize).toList)

  /** Representation of the transitions of a component from a state, as a pair
    * of parallel arrays, giving each possible event, and the list of
    * successor states, respectively. */
  type Trans = (ArrayBuffer[EventInt], ArrayBuffer[List[State]])

  /** The transitions of the components: Map from states to a pair of parallel
    * arrays, giving each possible event, and the list of successor states,
    * respectively.  Built in initTransitions.  */
  private var transMap = Map[State, Trans]()

  /** The initial states of each type. */
  private val inits: Array[Array[State]] =
    Array.tabulate(numFamilies)(i => new Array[State](idSizes(i)))

  /** The representation of the event tau. */
  // @inline private val Tau = 1

  /** Bit map, indexed by events, showing whether each event is in the alphabet
    * of these components.  Initialised by initAlphas.  */
  var alphaBitMap: Array[Boolean] = null

  /** Map that gives, for each event e, the identities of components that
    * synchronise on e.  Initialised by initAlphas. */
  private var eventMap: Array[List[ProcessIdentity]] = null

  /** List of passive components that synchronise on each event; indexed by 
    * events.  Initialised by initAlphas. */
  var passiveCptsOfEvent: Array[List[ProcessIdentity]] = null

  def getEventMap = eventMap

  /** Show a particular event.  Now in package. */
  //private def showEvent(e: EventInt) = fdrSession.eventToString(e)

  // Set global variable: the type identifiers of the indexing types,
  // by component family.
  indexingTypes = fdrTypeIds.map(ti => fdrEvents.fdrTypeToType(ti))
  println("indexingTypes = "+indexingTypes.mkString(", "))

  // Set global variable: the names of types. 
  typeNames = 
    (0 until numTypes).map(i => 
      familyTypeNames(indexingTypes.indexOf(i))).toArray
  println("typeNames = "+typeNames.mkString(", "))

  /** Build transition system for components in transMap, and alphabets for each
    * component in alphas, initial states in inits. */
  private def init() = {
    println("Building component alphabets")
    initAlphas() // Initialise eventMap and alphaBitMap
    println("Building component transitions")
    initTransitions()

    // For the ith family, the number of identities should be the same as the 
    // number of values in the corresponding type.
    assert((0 until numFamilies).forall(i => 
             idSizes(i) == typeSizes(indexingTypes(i))),
           idSizes.mkString("(",",",")")+"; "+typeSizes.mkString("(",",",")"))

    // Set maxSubtypeSize and build eventBitMap (note the former is
    // necessary for the latter).  IMPROVE: at present, typeSizes is
    // set in initTransitions; can this be moved into initAlphas?
    maxSubtypeSize = idSizes.max
    println("maxSubtypeSize = "+maxSubtypeSize)
    assert(maxSubtypeSize > 0)
  }

  /** Initialise information relevant to the alphabets: eventMap, alphaBitMap
    * and passiveCptsOfEvent. */
  private def initAlphas() = { 
    // Build alphabets: alphas(pt)(j) gives the alphabet of the jth element
    // (identity idTypes(pt)(j)) from process type pt.
    val alphas: Array[Array[scala.collection.immutable.Set[EventInt]]] =
      Array.tabulate(numFamilies)( f =>
        new Array[scala.collection.immutable.Set[EventInt]](idSizes(f)))
    // All events 
    val allEvents = scala.collection.mutable.Set[EventInt]()
    // IMPROVE: can the following be done in parallel? 
    for(f <- 0 until numFamilies; i <- indices(f)){
      // String representing name of alphabet of this process
      val alphaSt = alphaNames(f)+"("+idTypes(f)(i)+")"
      print(s"Building $alphaSt ...")
      // Corresponding list of event names
      val alphaList: Array[String] = 
        // fdrSession.setStringToList(alphaSt)
        fdrSession.evalSeqSeqOrSeq(alphaSt, st => st) 
      // Convert to EventInts, and store
      val eventIntList = alphaList.map(fdrEvents.eventToInt(_))
      alphas(f)(i) = eventIntList.toSet
      allEvents ++= eventIntList // alphas(f)(i)
      println(s"(${alphaList.length} events).  Done.")
    }

    // eventMap, maps each event e to the list of identities of processes that
    // synchronise on e.
    eventMap = new Array[List[Parameter]](eventsSize)
    // alphaBitmap shows which events are in alphabet
    alphaBitMap = new Array[Boolean](eventsSize)
    // passiveCptsOfEvent show the passive component (if any) involved in each
    // event.
    passiveCptsOfEvent = new Array[List[Parameter]](eventsSize)
    for(e <- (0 until eventsSize)/*.par*/){ // IMPROVE: par?
      eventMap(e) = 
        (for(f <- 0 until numFamilies;
             i <- indices(f); if (alphas(f)(i).contains(e)))
         yield (f,i)).toList
      assert(eventMap(e).length <= 2,
             "Event "+showEvent(e)+" synchronised on by "+
               eventMap(e).length+" components.")
      passiveCptsOfEvent(e) = eventMap(e).filter{ case(f,_) => !actives(f)}
      assert(passiveCptsOfEvent(e).length <= 1, 
        s"Event ${showEvent(e)} synchronised on by more than one passive component.")
      alphaBitMap(e) = allEvents.contains(e)
    }
    //passiveCptsOfEvent = eventMap.map(_.filter{ case(f,_) => !actives(f) })
  }

  /** Initialise model of the transition systems: inits and transMap. */
  private def initTransitions() = {
    // Build transitions
    for(pt <- 0 until numFamilies){
      println("Building transitions for type "+processNames(pt))
      //val seen = Set[State]() // states seen so far
      //val transMap0 = Map[State, List[(EventInt, State)]]()

      for(i <- indices(pt)){
        // Build raw state machines for ith component.
        val t = idTypes(pt)(i); val id = fdrSession.symmetryValue(t)
        val procName = processNames(pt)+"("+t+")"
        print("Building "+procName+"...")
        // Note: FDR performs its part of evalProc sequentially, so there's
        // little to be gained by trying to do the following concurrently.
        val machine = fdrSession.evalProc(procName)
        // Build transition map
        val seen = Set[State]() // states seen so far
        val transMap0 = Map[State, List[(EventInt, State)]]()
        inits(pt)(i) = transMapBuilder.augmentTransMap(
          transMap0, seen, machine, pt, id, fdrTypeIds(pt))

        // Now convert into more convenient form, copying into transMap, giving
        // a map from states to parallel ArrayBuffers, giving possible events
        // and next states.
        println(s".  ${seen.size} states.")
        // val oRenamingName = renames(pt).map(_+s"($t)")
        // val renamingMap = transMapBuilder.mkRenamingMap(oRenamingName)
        val renamingMap = transMapBuilder.mkRenamingMap(renames(pt), t)

        // IMPROVE: use parallel here
        for(s <- seen){
          // Transitions still to consider
          var transList: List[(EventInt, State)] = 
            if(renamingMap == null) transMap0(s)
            else transMapBuilder.renameTransList(transMap0(s), renamingMap)
          // println(s"transList = "+transList.map{ case (e,post) =>
          //   s"${s.toString00} -$e${showEvent(e)}-> ${post.toString00}" })
          // Result for this state.
          val transListEvent = new ArrayBuffer[EventInt]
          val transListNexts = new ArrayBuffer[List[State]]
          for(e <- 0 until eventsSize /*numEvents */){
            assert(transList.isEmpty || transList.head._1 >= e)
            val (matches, rest) = transList.span(_._1 == e)
            transList = rest
            if(matches.nonEmpty){
              transListEvent += e; transListNexts += matches.map(_._2)
              // for(post <- matches.map(_._2)) 
              //   println(s"${s.toString00} -${showEvent(e)}-> ${post.toString00}")
            }
          }
          assert(transList.isEmpty)
          transMap.synchronized{ transMap(s) = (transListEvent, transListNexts) }
        } // end of for(s <- seen.par)
      } // end of for (i <- indices(pt)
    } // end of for(pt <- ...)
  } // end of initTransitions

  // Do the initialisation. 
  init()

  // -------------------------------------------------------

  private type Trans1 = (Array[EventInt], Array[Array[State]])

  private val EmptyStateArray = Array[State]()

// IMPROVE: these objects use a lot of memory. 
  /** Representation of the transitions from a state.  Transitions are
    * represented by parallel arrays of events (terminated with Sentinel) and
    * lists of next-states.  eventsServer and nextsServer give transitions
    * synchronising with no other component, but synchronising with the
    * server.  eventsSolo and nextsSolo give transitions synchronising with no
    * other component, nor with the server.  transComponent(f)(i) represents
    * transitions synchronised with the component with process identity (f,i);
    * except null is used to repsesent no transitions (for compactness).
    * transServerComponent(f)(i) represents transitions synchronising with
    * server and component (f,i).  */ 
  class ComponentTransitions(
    val eventsServer: Array[EventInt], val nextsServer: Array[Array[State]],
    val eventsSolo: Array[EventInt], val nextsSolo: Array[Array[State]],
    val transComponent: Array[Array[Trans1]], 
    val transServerComponent: Array[Array[Trans1]]
  ){
    /** The next states possible after event e synchronising with component
      * (f,i). */
    def nexts(e: EventInt, f: Family, id: Identity): Array[State] = {
      val ens = transComponent(f)(id)
      if(ens != null){ val (es, ns) = ens; binSearch(e, es, ns) }
      else{ 
        val ens1 =  transServerComponent(f)(id)
        if(ens1 != null){ val (es,ns) = ens1; binSearch(e, es, ns) }
        else EmptyStateArray 
      }
    }

    @inline private def binSearch(
      e: EventInt, es: Array[EventInt], ns: Array[Array[State]])
        : Array[State] = {
      var i = 0; var j = es.length-1; assert(es(j) == Sentinel)
      // Binary search for e.  Inv es[0..i) < e <= es[j..)
      while(i < j){
        val m = (i+j)/2 // i <= m < j
        if(es(m) < e) i = m+1 else j = m
      }
      // es[0..i) < e <= es[i..m)
      if(es(i) == e) ns(i) else EmptyStateArray // Array() 
    }

  } // end of class ComponentTransitions

  // -------------------------------------------------------

  /** Map giving the transitions from a state. */ 
  private val transComponentStore = Map[State, ComponentTransitions]()
  /* Note: the above is created (sequentially) during initialisation,
   * and then read during the search, so doesn't need to be
   * protected. */

  /** Build a map, categorising transitions from each state as a value of type
    * ComponentTransitions, and storing these. */
  def categoriseTrans(serverAlphaBitMap: Array[Boolean]) = {
    // To save memory, we share singleton arrays of states.
    val singletonStateMap = Map[State, Array[State]]()
    for((st,_) <- transMap.iterator) singletonStateMap += st -> Array(st)
    /* Convert nexts to an array, reusing arrays for singletons. */
    @inline def getStateArray(nexts: List[State]): Array[State] = {
      assert(nexts.nonEmpty)
      if(nexts.length == 1) singletonStateMap(nexts.head)
      else nexts.toArray
    }

    for((st, (events0, nexts0)) <- transMap.iterator){
      // Build up transitions in following; names match the parameters of
      // ComponentTransitions.
      val eventsSolo = new ArrayBuffer[EventInt]
      val nextsSolo = new ArrayBuffer[Array[State]]
      val eventsServer = new ArrayBuffer[EventInt]
      val nextsServer = new ArrayBuffer[Array[State]]
      val transComponent, transServerComponent = Array.tabulate(numFamilies)(f =>
        Array.fill(idSizes(f))(
          (new ArrayBuffer[EventInt], new ArrayBuffer[Array[State]])
        ) )

      var i = 0; var n = events0.length
      if(n > 0 && events0(0) == Tau){ 
        eventsSolo += Tau; nextsSolo += getStateArray(nexts0(0)); i = 1
      }
      val me: Parameter = st.componentProcessIdentity 
      while(i < n){
        val e = events0(i); val nexts = nexts0(i); val cpts = eventMap(e); 
        assert(cpts.contains(me), 
               "Event "+showEvent(e)+" is not in the alphabet of component "+me+
                 "\n"+cpts+"\n"+
                 (if(st==null) "null state" else st.toString00)+"\n"+
                 events0.map(showEvent).mkString("<",",",">"))
        // IMPROVE: translate "me" into human-friendly form
        if(cpts.length == 1){
          if(serverAlphaBitMap(e)){
            eventsServer += e; nextsServer += getStateArray(nexts)
          }
          else{ eventsSolo += e; nextsSolo += getStateArray(nexts)}
        }
        else{ // sync with one other component
          assert(cpts.length == 2); val head = cpts.head
          // the other component synchronising on e
          val (f,i) = if(head == me) cpts.tail.head else head
          val (es,nextss) =
            if(serverAlphaBitMap(e)) transServerComponent(f)(i)
            else transComponent(f)(i)
          es += e; nextss += getStateArray(nexts) 
        }
        i += 1
      }
      // Add sentinels.
      eventsServer += Sentinel; eventsSolo += Sentinel
      // Add sentinels in transComponent, transServerComponent; replace empty
      // items with null
      val transComponent1, transServerComponent1 = 
        Array.tabulate(numFamilies)(f => new Array[Trans1](idSizes(f)))
      for(f <- 0 until numFamilies; i <- 0 until idSizes(f)){
        val (es,nexts) = transComponent(f)(i)
        if(es.nonEmpty){ 
          es += Sentinel; transComponent1(f)(i) = (es.toArray, nexts.toArray)
        }
        else transComponent1(f)(i) = null
        val (es1,nexts1) = transServerComponent(f)(i)
        if(es1.nonEmpty){
          es1 += Sentinel;
          transServerComponent1(f)(i) = (es1.toArray, nexts1.toArray)
        }
        else transServerComponent1(f)(i) = null
      }
      // Create and store ComponentTransitions object
      val trans1 = new ComponentTransitions(
        eventsServer.toArray, nextsServer.toArray, 
        eventsSolo.toArray, nextsSolo.toArray, 
        transComponent1, transServerComponent1)
      transComponentStore += st -> trans1
    } // end of for
    transMap = null // for GC
  }

  // --------- Functions used during the main check ---------

  /** Initial views of components.
    * @return an array of pairs (princ, others), where princ will be the 
    * principal component in a ComponentView, and others will be those
    * referenced by princ. */
  def initViews(servers: ServerStates): Array[ComponentView] = { 
    val fInits = inits.flatten
    fInits.map(princ => 
      new ComponentView(servers, StateArray.referencedStates(princ, fInits)))
  }

  /** Get the transitions of the component in state st. */
  def getTransComponent(st: State): ComponentTransitions =
    try{ transComponentStore(st) }
    catch {
      case e: NoSuchElementException =>
        println(s"Impossible state ${st.toString0} of type "+
          familyNames(st.family)+" encountered.\n"+
          "This probably means that the script contains too few identities,\n"+
          "or the state spaces are not symmetric.")
        assert(!st.representableInScript)
        throw new InsufficientIdentitiesException
    }
}

