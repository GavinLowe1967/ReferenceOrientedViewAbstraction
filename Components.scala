package ViewAbstraction

//import uk.ac.ox.cs.fdr.{Option => _}
import scala.collection.JavaConverters._
import scala.collection.mutable.{Map,Set,ArrayBuffer}
// import scala.collection.parallel.CollectionConverters._
// import ox.cads.util.Profiler

/** Model of the replicated components, possibly comprising multiple families
  * of processes.
  * 
  * @param processNames the process name (from the script) for each type of 
  * component process.
  * @param fdrTypeIds the representation of each type inside FDR. 
  * @param alphaNames the name of the alphabet for each type components process.
  */
class Components(
  fdrSession: FDRSession, transMapBuilder: FDRTransitionMap,
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
    * of these components. */
  var alphaBitMap: Array[Boolean] = null

  /** Map that gives, for each event e, the identities of components that
    * synchronise on e. */
  private var eventMap: Array[List[ProcessIdentity]] = null

  /** List of passive components that synchronise on each event; indexed by 
    * events. */
  var passiveCptsOfEvent: Array[List[ProcessIdentity]] = null

  def getEventMap = eventMap

  /** Show a particular event. */
  private def showEvent(e: EventInt) = fdrSession.eventToString(e)

  // Set global variable: the type identifiers of the indexing types,
  // by component family.
  indexingTypes = fdrTypeIds.map(ti => transMapBuilder.fdrTypeToType(ti))
  println("indexingTypes = "+indexingTypes.mkString(", "))

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

  /** Initialise information relevant to the alphabets: eventMap and
    * alphaBitMap. */
  private def initAlphas() = { 
    // Build alphabets: alphas(pt)(j) gives the alphabet of the jth element
    // (identity idTypes(pt)(j)) from process type pt.
    val alphas: Array[Array[scala.collection.immutable.Set[EventInt]]] =
      Array.tabulate(numFamilies)( f =>
        new Array[scala.collection.immutable.Set[EventInt]](idSizes(f)))
    // All events 
    val allEvents = scala.collection.mutable.Set[EventInt]()
//def initAlphas1 = {
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
      val eventIntList = alphaList.map(fdrSession.eventToInt(_))
      alphas(f)(i) = eventIntList.toSet
      allEvents ++= eventIntList // alphas(f)(i)
      println(s"(${alphaList.length} events).  Done.")
    }
//}

    // eventMap, maps each event e to the list of identities of processes that
    // synchronise on e.
    eventMap = new Array[List[Parameter]](eventsSize)
    // alphaBitmap shows which events are in alphabet
    alphaBitMap = new Array[Boolean](eventsSize)
//def initAlphas2 = {
    for(e <- (0 until eventsSize)/*.par*/){ // IMPROVE: par?
      eventMap(e) = 
        (for(f <- 0 until numFamilies;
             i <- indices(f); if (alphas(f)(i).contains(e)))
         yield (f,i)).toList
      assert(eventMap(e).length <= 2,
             "Event "+showEvent(e)+" synchronised on by "+
               eventMap(e).length+" components.")
      alphaBitMap(e) = allEvents.contains(e)
    }
    passiveCptsOfEvent = eventMap.map(_.filter{ case(f,_) => !actives(f) })
//}

//    initAlphas1; initAlphas2 //; initAlphas3
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

  /** Representation of the transitions from a state. */ 
  class ComponentTransitions{
    /* Transitions are represented by parallel arrays of events (terminated with
     * Sentinel) and lists of next-states. */

    // Those transitions synchronising with no other component, and
    // synchronising with the server.
    val eventsServer = new ArrayBuffer[EventInt]
    val nextsServer = new ArrayBuffer[List[State]]

    // Those transitions synchronising with no other component, nor with the
    // server.
    val eventsSolo = new ArrayBuffer[EventInt]
    val nextsSolo = new ArrayBuffer[List[State]]

    /** Transitions synchronising with one other component:
      * transComponent(f)(i) represents transitions synchronised with
      * the component with process identity (f,i); except null is used
      * to repsesent no transitions (for compactness). */
    val transComponent = Array.tabulate(numFamilies)(f =>
      Array.fill[Trans](idSizes(f))(
        (new ArrayBuffer[EventInt], new ArrayBuffer[List[State]])
      ) )

    /** Transitions synchronising with server and one other component:
      * representation is as for transComponent. */
    val transServerComponent = Array.tabulate(numFamilies)(f =>
      Array.fill[Trans](idSizes(f))(
        (new ArrayBuffer[EventInt], new ArrayBuffer[List[State]])
      ) )

    /** Add sentinels, and replace empty sets of transitions in transComponent by
      * null. */
    def finish = {
      // Add sentinels
      eventsServer += Sentinel; eventsSolo += Sentinel
      for(f <- 0 until numFamilies; i <- 0 until idSizes(f)){
        val es = transComponent(f)(i)._1
        if(es.nonEmpty) es += Sentinel else transComponent(f)(i) = null
        val es1 = transServerComponent(f)(i)._1
        if(es1.nonEmpty) es1 += Sentinel else transServerComponent(f)(i) = null
      }
    }
    // IMPROVE: use Arrays instead of ArrayBuffers?  Compress more?

    /** The next states possible after event e synchronising with component
      * (f,i). */
    def nexts(e: EventInt, f: Family, id: Identity): List[State] = {
      val ens = transComponent(f)(id)
      if(ens != null){
        val (es, ns) = ens; binSearch(e, es, ns)
      }
      else{
        val (es, ns) = transServerComponent(f)(id); binSearch(e, es, ns)
      }
    }

    /** Find the next-states in ns corresponding to e. */ 
    @inline private def binSearch(
      e: EventInt, es: ArrayBuffer[EventInt], ns: ArrayBuffer[List[State]])
        : List[State] = {
      var i = 0; var j = es.length-1; assert(es(j) == Sentinel)
      // Binary search for e.  Inv es[0..i) < e <= es[j..)
      while(i < j){
        val m = (i+j)/2 // i <= m < j
        if(es(m) < e) i = m+1 else j = m
      }
      // es[0..i) < e <= es[i..m)
      if(es(i) == e) ns(i) else List()
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
    for((st, (events0, nexts0)) <- transMap.iterator){
      val trans1 = new ComponentTransitions
      var i = 0; var n = events0.length
      if(n > 0 && events0(0) == Tau){ 
        trans1.eventsSolo += Tau; trans1.nextsSolo += nexts0(0); i = 1
      }
      val me: Parameter = st.componentProcessIdentity 
      //println(s"categoriseTrans($me)")
      while(i < n){
        val e = events0(i); val nexts = nexts0(i)
        // print(showEvent(e)+"\t")
        val cpts = eventMap(e); 
        assert(cpts.contains(me), 
               "Event "+showEvent(e)+" is not in the alphabet of component "+me+
                 "\n"+cpts+"\n"+
                 (if(st==null) "null state" else st.toString00)+"\n"+
                 events0.map(showEvent).mkString("<",",",">"))
        // FIXME: translate "me" into human-friendly form
        if(cpts.length == 1){
          if(serverAlphaBitMap(e)){
            trans1.eventsServer += e; trans1.nextsServer += nexts
          }
          else{ trans1.eventsSolo += e; trans1.nextsSolo += nexts }
        }
        else{ // sync with one other component
          assert(cpts.length == 2)
          val head = cpts.head
          // the other component synchronising on e
          val (f,i) = if(head == me) cpts.tail.head else head
          val (es,nextss) =
            if(serverAlphaBitMap(e)) trans1.transServerComponent(f)(i)
            else trans1.transComponent(f)(i)
          es += e; nextss += nexts
        }
        i += 1
      }
      trans1.finish
      transComponentStore += st -> trans1
    } // end of for
    transMap = null // for GC
    // eventMap = null // IMPROVE: do this; also the ref to this in Servers
  }

  // --------- Functions used during the main check ---------

  /** Initial views of components.
    * @return an array of pairs (princ, others), where princ will be the 
    * principal component in a ComponentView, and others will be those
    * referenced by princ. */
  def initViews(servers: ServerStates): Array[View] = { 
    val fInits = inits.flatten
    fInits.map(princ => 
      new ComponentView(servers, princ, View.referencedStates(princ, fInits)))
  }

  //   val iv = Views.alpha(aShapes, inits.flatten, true)
  //   // println("aShapes = "+aShapes.map(_.mkString("<", ",", ">")))
  //   // Check that for each family f, there are enough identities to produce an
  //   // initial view with all components in the same control state.
  //   for(f <- 0 until numFamilies){
  //     val maxf = aShapes.map(_(f)).max // max cpts of f in any shape
  //     // println(s"$f max number = $maxf")
  //     // Test if v satisfies the condition
  //     def ok(v: Views.View) = {
  //       val vf = v.filter(_.family == f)
  //       vf.length == maxf && vf.map(_.cs).distinct.length == 1
  //     }
  //     if(!iv.exists(ok)){
  //       println("Not enough identities of family "+familyTypeNames(f)+
  //                 " to produce initial view with all components in default state.");
  //       sys.exit
  //     }
  //   } 
  //   iv
  // }

  /** Get the transitions of the component in state st. */
  def getTransComponent(st: State): ComponentTransitions =
    try{ transComponentStore(st) }
    catch {
      case e: NoSuchElementException =>
        println("Impossible state "+st+" of type "+familyNames(st.family)+
                  " encountered.\n"+
                  "This probably means that the state spaces are not symmetric.")
        sys.exit
    }
}

