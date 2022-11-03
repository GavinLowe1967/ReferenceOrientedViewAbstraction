package ViewAbstraction.SystemP

import ViewAbstraction._
import ViewAbstraction.RemapperP.Remapper
// import ViewAbstraction.CombinerP.Combiner
import uk.ac.ox.cs.fdr.{Option => _, _}
import scala.collection.JavaConverters._
import scala.collection.mutable.{Map,Stack,Set,ArrayBuffer,HashMap}
import ox.gavin.profiling.Profiler

/** An object that creates the System corresponding to the CSP file fname.
  * @param checkDeadlock are we checking for deadlock? */
class System(fname: String) {
  var verbose = false

  /** The parser of the annotations in the CSP file. */
  private val file: CSPFileParser =
    try{ new CSPFileParser(fname) }
    catch {
      case error: java.io.FileNotFoundException => println(error); sys.exit()
      case error: InputFileError => println(error); sys.exit()
      case error: FileLoadError => println(error); sys.exit()
    }
 
  /** Object encapsulating the FDR session. */
  protected[SystemP] val fdrSession = new FDRSession(fname)


  /** Names of symmetric subtypes, indexed by component family number. */
  familyTypeNames = file.identityTypes.toArray

  assert(familyTypeNames.length == numFamilies && 
           familyTypeNames.distinct.length == numTypes)

  familyNames = file.componentProcessNames.toArray

  /** Names of supertypes of symmetric subtypes, indexed by component
    * family number. */
  private val superTypeNames: Array[String] =
    familyTypeNames.map(fdrSession.getSuperType(_))

  /** Object storing the events. */
  val fdrEvents = new FDREvents(fdrSession, superTypeNames)

  // Store in package object
  eventPrinter = fdrEvents
  compiling = true

  /** Convert event represented by e to the String corresponding to the
    * script. */
  // def showEvent(e: EventInt) = fdrSession.eventToString(e)

  // Set the number of visible events.  The visible events are numbered in
  // [3..fdrSession.numEvents+3), so we initialise arrays indexed by events to
  // size fdrSession.numEvents+3.
  private val numEvents = fdrEvents.numEvents
  eventsSize = numEvents+3

  fdrEvents.initEvents(eventsSize)

  scriptNames = fdrEvents.getNameMap

  /** The internal representation of each type inside FDR. */
  private val fdrTypeIds =
    Array.tabulate(numFamilies)(i => fdrSession.getTypeInt(familyTypeNames(i))) 

  /** Builder of transition systems. */
  private val transMapBuilder = new FDRTransitionMap(fdrSession, fdrEvents)

  println("Creating components")

  private val actives = file.componentActives.toArray

  private val activeFamilies = (0 until numFamilies).filter(actives(_))
  private val passiveFamilies = (0 until numFamilies).filter(!actives(_))
  println(s"Active families: $activeFamilies; passive families: $passiveFamilies")

  /** Model of the replicated components. */
  private val components = new Components(
    fdrSession, fdrEvents, transMapBuilder, fdrTypeIds,
    familyNames, file.componentAlphabets.toArray, 
    file.componentRenames.toArray, actives)

  // Store (in package object) an upper bound on component control states
  numCptControlStates = transMapBuilder.getMaxCS+1

  /** The size of each indexing subtype, by type number. */
  private val idSizes = typeSizes

  // Pools.init(typeSizes); 
  IdentitiesBitMap.init(typeSizes)

  /** The size of each indexing subtype, by component family number. */
  private val indexingTypeSizes = 
    familyTypeNames.map(fdrSession.getTypeValues(_).length).toArray
  // IMPROVE: this repeats work in Components

  /** Alphabet of components: componentAlphaBitMaps(e) is true if e is in the
    * alphabet of the components. */
  private val componentAlphaBitMap = components.alphaBitMap 

  /** Is v a ComponentView for an active component? */
  def isActive(cv: ComponentView) = actives(cv.principal.family)

  /** Model of the servers. */
  val servers =
    new Servers(file, fdrSession, fdrEvents, transMapBuilder,
                components.getEventMap, indexingTypeSizes)

  /** Names of servers. */
  def serverNames = servers.serverNames

  private def init() = {
    // Create the mapping from control states to types of parameters
    transMapBuilder.createStateTypeMap

    // Split transitions of components, based on which processes they
    // synchronise with.
    components.categoriseTrans(servers.alphaBitMap)

    //scriptNames = fdrEvents.getNameMap

    val cptEventMap: Array[List[ProcessIdentity]] = 
      components.getEventMap
    val serverAlphaMap: Array[Boolean] = servers.alphaBitMap

    // Set max sizes of maps needed in remappings.  This is a bit arbitrary.
    remapSizes = typeSizes.map(_+2)

    // find three-way synchronisations
    assert(cptEventMap.length == eventsSize, 
      s"${cptEventMap.length}; $numEvents")
    assert(serverAlphaMap.length == eventsSize, 
           s"${serverAlphaMap.length}; $numEvents; ${showEvent(numEvents+2)}")

    for(oi <- file.omitInfos) processOmitInfo(oi)

    fdr.libraryExit(); fdrSession.delete
    MyStateMap.renewStateStore // switch to trie-based state store
    compiling = false // global variable
  }

  init()

  /** Process the omit information from the file.  We build a partial mapping
    * from control states to bitmaps, showing which referenced states are
    * omitted. */
  private def processOmitInfo(omitInfo: OmitInfo) = {
    println(s"\nProcessing $omitInfo") 
    val OmitInfo(processName, params, omits) = omitInfo

    // Map over indices of params, giving the type identifier if the parameter
    // is from an identity type, otherwise -1.
    val indexingTypes = params.map{ case (p,t) => familyTypeNames.indexOf(t) }
    // Number of such parameters
    val numDistinguished = indexingTypes.count(_ >= 0)

    // Check each omitted value corresponds to an identity type, and is not
    // the principal.
    val argNames = params.map(_._1)
    for(om <- omits){
      // Index of om in the parameters
      val ix = argNames.indexOf(om) 
      assert(ix != 0, s"Cannot omit principal of process $processName")
      assert(indexingTypes(ix) >= 0,
        "Type "+params(ix)._2+
          " of omitted reference is not a distinguished type.")
    }

    // Bitmap showing which parameters of syntactic states will be included.
    // includeBitMap(i) is true if the ith identity parameter is included (not
    // omitted).
    val includeBitMap = new Array[Boolean](numDistinguished)
    var i = 0; var j = 0
    while(j < params.length){
      if(indexingTypes(j) >= 0){ 
        includeBitMap(i) = !omits.contains(params(j)._1);  i += 1 
      }
      j += 1
    }

    // The values in the types of the parameters
    val typeValues: List[List[String]] = 
      params.map{ case(p,t) => fdrSession.getTypeValues(t) }
    // All values for the parameters.  In each element of distVals, if the ith
    // value is Some(x) then the ith parameter is an identity parameter that
    // can take value x; if the ith value is None, the ith parameter is not an
    // identity parameter.
    val distVals: List[List[Option[String]]] = 
      cp(typeValues, indexingTypes.map(_ >= 0))

    // List of distinct values to instantiate the identity parameters.  Used
    // to work out which syntactic parameter ends up as which parameter of
    // resulting states.
    var distinctParams = List[Parameter]()
    // Corresponding list of names of the identity parameters (as Some _)
    // terms), interspersed with None in the place of non-identity parameters.
    var distinctParamNames = List[Option[String]]()
    // For each type, the index of the next value of that type to use.
    val nextVal = new Array[Int](numTypes)
    for(i <- params.length-1 to 0 by -1){ // build from right to left
      val t = indexingTypes(i)
      if(t >= 0){
        distinctParams ::= ((t, nextVal(t))); val v = typeValues(i)(nextVal(t))
        distinctParamNames ::= Some(v); nextVal(t) += 1
      }
      else distinctParamNames ::= None
    }

    // All values for the non-distinguished types
    val nonDistVals = cp(typeValues, indexingTypes.map(_ < 0))

    // Get the control state and parameters corresponding to processName with
    // parameters the merger of nd and dv.
    def getProcInfo(nd: List[Option[String]], dv: List[Option[String]])
        : (ControlState, List[Parameter]) = {
      val idStrings = merge(nd, dv)
      val procString = processName+idStrings.mkString("(", ",", ")")
      if(false) print(procString+": ")
      val (cs,ids) = transMapBuilder.getProcInfo(procString)
      if(false) println((cs,ids).toString)
      println(s"$procString: ($cs,$ids)")
      (cs,ids)
    }

    for(nd <- nonDistVals){
      val (cs,ids) = getProcInfo(nd, distinctParamNames)
      if(State.isReachable(cs)){
        // ids should be a permutation of distinctParams.  Build the bijection
        // from the indices of ids (parameters of States) to the indices of
        // distinctParams (syntactic parameters).
        val pi = ids.map(p => distinctParams.indexOf(p))
        assert(pi.forall(_ >= 0))
        // And the other way
        val piInv = distinctParams.map(p => ids.indexOf(p))
        assert(piInv.forall(_ >= 0))

        // Bit map showing which referenced parameters of this state will be
        // included: the ith of a State component corresponds to the pi(i)'th
        // syntactic parameter.
        val thisBitMap = 
          Array.tabulate(numDistinguished)(i => includeBitMap(pi(i)))
        val f = State.stateTypeMap(cs)(0)
        println(s"Storing omit information $cs (family $f) -> "+
          thisBitMap.mkString(", "))
        assert(passiveFamilies.contains(f),
          "Only passive families can have omit information.  Process "+
            processName+" is from an active family.")
        State.setIncludeInfo(cs, thisBitMap)

// FIXME: if a process can transition from a state where certain views are
// omitted to a state where the corresponding views are included, then we
// won't always find the latter.  The code should check that this doesn't
// happen.  (At present, it's a requirement on the user.)

        // Check all others agree.  This is very slow
        if(false){
          print("Checking consistency\n")
          for(dv <- distVals){
            val (cs1,pids) = getProcInfo(nd, dv); assert(cs1 == cs)
            // Traverse through dv and ids, checking they correspond
            var i = 0; var j = 0
            while(j < dv.length){
              if(dv(j).nonEmpty){
                assert(dv(j).get == typeValues(j)(pids(piInv(i))._2), 
                  s"dv = $dv \n pids = $pids \n typeValues = $typeValues $i $j")
                i += 1
              }
              j += 1
            }
          }
          println()
        } // end of if(false)
      }
      else println(s"Control state $cs not reachable")
    }
  }

  /* Cartesian product of values from typeValues(i) such that flags(i), wrapping
   * such values as Some(_) values, and using None where !flags(i). */
  private def cp(typeValues: List[List[String]], flags: List[Boolean])
      : List[List[Option[String]]] = {
    if(typeValues.isEmpty){ assert(flags.isEmpty); List(List()) }
    else{
      val rest = cp(typeValues.tail, flags.tail)
      if(flags.head) typeValues.head.flatMap(v => rest.map(r => Some(v)::r))
      else rest.map(None::_)
    }
  }

  /** The merge of dv and nd.  The two lists are expected to have Some values in
    * opposite positions. */ 
  private def merge(dv: List[Option[String]], nd: List[Option[String]])
      : List[String] = {
    if(dv.isEmpty){ assert(nd.isEmpty); List() }
    else{
      val dv0 = dv.head; val nd0 = nd.head; val rest = merge(dv.tail, nd.tail)
      if(dv0.nonEmpty){ assert(nd0.isEmpty); dv0.get::rest }
      else nd0.get::rest
    }
  }

  /** Representation of the event error. */
  val Error = fdrEvents.eventToInt("error")

  /** Finaliser.  Should be called on exit. */
  def finalise = fdr.libraryExit()

  // At end of construction, close FDR.
  finalise

  /** The initial system views. */
  def initViews: (ViewSet, Array[ComponentView]) = {
    val serverInits: List[State] = servers.inits
    val viewSet: ViewSet = 
      if(UseNewViewSet) new NewViewSet else new ServerPrincipalBasedViewSet(16)
    val activeViews = new ArrayBuffer[ComponentView]
    // All views 
    val views = components.initViews(ServerStates(serverInits))
    for(v <- views){
      val v1 = Remapper.remapView(v)
      if(verbose) 
        println(v.toString+" -> "+v1.toString+(if(isActive(v)) "*" else ""))
      if(viewSet.add(v1)){ activeViews += v1; if(verbose) println("**") }
    }
    (viewSet, activeViews.toArray)
  }
  
  /** We represent sets of transitions corresponding to a ComponentView cv using
    * lists of tuples of type TransitionRep.  Each tuple (pre, e, post, pid)
    * represents concrete transitions pre U new U cpts -e-> post U new' U
    * cpts, for each set new and new', cpts such that: (1) if pid is non-null,
    * then new, new' have component identity pid and transition new -e-> new';
    * otherwise new and new' are absent; (2) the three parts have disjoint
    * identities.  The concretizations pre and post contain the same component
    * identities, namely those identities in cv.
    */
  type TransitionRep = 
    (Concretization, EventInt, Concretization, ProcessIdentity)

  /** The transitions caused by the principal component of cv. 
    * @return a list of tuples (pre, e, post, pids) representing concrete 
    * transitions pre U new U cpts -e-> post U new' U cpts, for each set new
    * and new', cpts such that: (1) new, new' have component identities pIds
    * and transition new -e-> new'; (2) the three parts have disjoint
    * identities.  The concretizations pre and post contain the same component
    * identities, namely those identities in cv; in fact, pre is the
    * concretization corresponding to cv (IMPROVE). */
  def transitions(cv: ComponentView): List[TransitionRep] = {
    var result = List[TransitionRep]()
    // Add an element to result if it's canonical
    def maybeAdd(pre: Concretization, e: EventInt, post: Concretization, 
        pid: ProcessIdentity) =
      if(isCanonicalTransition(pre, post)) result ::= ((pre, e, post, pid)) 
      else if(verbose) println(s"Not cannonical $pre -${showEvent(e)}-> $post")

    val princTrans = components.getTransComponent(cv.principal)
    val (pf,pi) = cv.principal.componentProcessIdentity
    val pParams = cv.principal.processIdentities
    val serverTrans: servers.ServerTransitions = 
      servers.transitions(cv.servers.servers)

    // IMPROVE: the transitions probably aren't in the best form
    val conc0 = Concretization(cv)
    val activePrincipal = isActive(cv) // is the principal active

    // Case 1: events of the principal component with no synchronisation
    if(activePrincipal) 
      for(i <- 0 until princTrans.eventsSolo.length-1;
        st1 <- princTrans.nextsSolo(i)){
        val newCpts = cv.components.clone; newCpts(0) = st1
        val post = new Concretization(cv.servers, StateArray(newCpts)) 
        maybeAdd(conc0, princTrans.eventsSolo(i), post, null)
      }

    // Case 2: synchronisation between principal component and server (only)
    val serverTrans1 = serverTrans.transSync(pf)(pi)
    if(serverTrans1 != null){
      val (sEs, sNexts):
          (ArrayBuffer[EventInt], ArrayBuffer[List[List[State]]]) = serverTrans1
      val pEs = princTrans.eventsServer; val pNexts = princTrans.nextsServer
      // Search for synchronisations
      var serverIndex = 0; var cptIndex = 0 // indexes for server, princ cpt
      var sE = sEs(0); var pE = pEs(0) // next events
      while(sE < Sentinel && pE < Sentinel){
        while(sE < pE){ serverIndex += 1; sE = sEs(serverIndex) }
        if(sE < Sentinel){
          while(pE < sE){ cptIndex += 1; pE = pEs(cptIndex) }
          if(sE == pE){ // can synchronise
            if(activePrincipal || servers.isActiveServerEvent(sE)){
              //if(!activePrincipal) println("server-only event: "+showEvent(sE))
              // println(s"Server-principal sync on ${showEvent(pE)}")
              for(pNext <- pNexts(cptIndex); sNext <- sNexts(serverIndex)){
                val newCpts = cv.components.clone; newCpts(0) = pNext
                val post = 
                  new Concretization(ServerStates(sNext), StateArray(newCpts))
                maybeAdd(conc0, sE, post, null)
              }
            }
            serverIndex += 1; sE = sEs(serverIndex)
            cptIndex += 1; pE = pEs(cptIndex)
          }
        }
      }
    }

    // Case 3: events synchronising principal component and one component.
    if(activePrincipal) for(f <- passiveFamilies; id <- 0 until idSizes(f)){
      // Synchronisations with (f,id)
      val theseTrans = princTrans.transComponent(f)(id)
      val componentIx = // index of (f,id) in components, or -1
        StateArray.findIndex(cv.components, f, id)
      assert(componentIx != 0)
      val isOmitted = // reference to (f,id) but omitted from cv
        componentIx < 0 && pParams.contains((f,id))
      if(isOmitted) assert(singleRef) // IMPROVE
      // If isOmitted, we suppress these transitions: we'll find them from a
      // different view including (f,id)
      if(theseTrans != null && !isOmitted){ 
        val (oEs, oNs): (Array[EventInt], Array[Array[State]]) = 
          theseTrans
        // Find id of relevant component; find compatible states of that
        // component.
        for(i <- 0 until oEs.length-1){
          val e = oEs(i); assert(i < Sentinel)
          assert(components.passiveCptsOfEvent(e) == List((f,id)))
          if(componentIx >= 0){ // the passive component is present
            val passiveSt = cv.components(componentIx) 
            // Next states for the present passives
            val pNexts = components.getTransComponent(passiveSt).nexts(e, pf, pi)
            for(pNext <- pNexts){
              for(st1 <- oNs(i)){
                // Post-state of components
                val cptsPost = cv.components.clone; cptsPost(0) = st1;
                cptsPost(componentIx) = pNext
                val post = new Concretization(cv.servers, StateArray(cptsPost)) 
                maybeAdd(conc0, e, post, null)
              }
            }
          }
          else{ // the passive component is absent
            val conc0 = Concretization(cv)
            for(st1 <- oNs(i)){ // the post state of the principal cpt
              val newCpts = cv.components.clone; newCpts(0) = st1
              val post = new Concretization(cv.servers, StateArray(newCpts))
              maybeAdd(conc0, e, post, (f,id))
            }
          }
        } // end of for(i <- 0 until oEs.length-1)
      } // end of if(theseTrans != null)
    } // end of case 3

    // Case 4: events only of servers (typically the constructor, but also error)
    val sEsSolo = serverTrans.eventsSolo; val sNsSolo = serverTrans.nextsSolo
    var index = 0; var e = sEsSolo(0)
    while(e < Sentinel){
      for(newServers <- sNsSolo(index)){
        val post = new Concretization(ServerStates(newServers), cv.components)
        maybeAdd(conc0, e, post, null)
      }
      index += 1; e = sEsSolo(index)
    }

    // Case 5: events between server, principal component and one other
    // component. 
    val cptTrans2 = princTrans.transServerComponent
    if(activePrincipal) for(of <- passiveFamilies; oi <- 0 until idSizes(of)){
      // Synchronisations between principal, other component (of,oi) and
      // server, from principal's state, and then from server's state.
      val theseCptTrans: (Array[EventInt], Array[Array[State]]) =
        cptTrans2(of)(oi)
      val theseServerTrans
          : (ArrayBuffer[EventInt], ArrayBuffer[List[List[State]]]) =
        serverTrans.transSync2((pf,pi), (of,oi))
// IMPROVE: only if !singleRef
      val componentIx = // index of (f,id) in components, or -1
        cv.components.indexWhere(_.componentProcessIdentity == (of,oi))
      assert(componentIx != 0, s"cv = $cv, ($of, $oi)")
      val isOmitted = // reference to (f,id) but omitted from cv
        componentIx < 0 && pParams.contains((of,oi))
      // if(isOmitted && theseCptTrans != null && theseServerTrans != null)
      //   println(s"Omitting transition with ${(of,oi)} from $cv")
      if(isOmitted) assert(singleRef)
      if(theseCptTrans != null && theseServerTrans != null && !isOmitted){
        val (pEs,pNexts) = theseCptTrans; val (sEs, sNexts) = theseServerTrans
        // is the other component in cv?
        val otherIndices = (1 until cv.components.length).filter(i =>
          cv.components(i).componentProcessIdentity == (of,oi))
        // Scan through arrays, looking for synchronisations.  Indexes into
        // the arrays and corresp events: Inv: pE = pEs(pj), sE = sEs(sj)
        var pj = 0; var pE = pEs(pj); var sj = 0; var sE = sEs(sj)
        while(pE < Sentinel && sE < Sentinel){
          while(sE < pE){ sj += 1; sE = sEs(sj) }
          if(sE < Sentinel){
            while(pE < sE){ pj += 1; pE = pEs(pj) }
            if(sE == pE && (activePrincipal || servers.isActiveServerEvent(sE))){ 
              // can synchronise
              assert(activePrincipal) // I think the other case can't happen
              if(otherIndices.nonEmpty){
                if(verbose)
                  println("Synchronisation: "+cv+"; "+showEvent(sE)+": "+
                    pNexts(pj)+"; "+sNexts(sj))
                assert(otherIndices.length == 1) // FIXME: could have two refs 
                val otherIndex = otherIndices.head
                val otherState = cv.components(otherIndex)
                // Synchronisations between otherState and the principal
                val otherNexts
                    : (Array[EventInt], Array[Array[State]]) =
                  components.getTransComponent(otherState).
                    transServerComponent(pf)(pi)
                if(otherNexts != null){
                  val (otherEs, otherStates) = otherNexts
                  var oj = 0;  while(otherEs(oj) < pE) oj += 1
                  if(otherEs(oj) == pE){
                    val pre = Concretization(cv)
                    // Possible next states of others
                    for(newServers <- sNexts(sj); newPrincSt <- pNexts(pj);
                        st <- otherStates(oj)){
                      val newCpts = cv.components.clone
                      newCpts(0) = newPrincSt; newCpts(otherIndex) = st
                      val post = new Concretization(
                        ServerStates(newServers), StateArray(newCpts))
                      maybeAdd(pre, sE, post, null)
                    }
                  }
                }
              } // end of otherIndices.nonEmpty
              else{
                val pre = Concretization(cv)
                for(newServers <- sNexts(sj); newPrincSt <- pNexts(pj)){
                  val newCpts = cv.components.clone; newCpts(0) = newPrincSt
                  val post = new Concretization(
                    ServerStates(newServers), StateArray(newCpts))
                  if(verbose)
                    println(s"Three-way synchronisation: "+
                      s"$pre -${showEvent(sE)}-> $post with ${(of,oi)}")
                  maybeAdd(pre, sE, post, (of,oi))
                }
              }

            } // end of if(sE == pE), synchronisation case
            if(sE == pE){ pj += 1; assert(pE != pEs(pj)); pE = pEs(pj) }
            sj += 1; assert(sE != sEs(sj)); sE = sEs(sj)
          }
        } // end of while(pE < Sentinel && sE < Sentinel)
      }
    } // end of for
    
    result
  }

  /** Is a transition canonical in the sense that fresh parameters that are
    * introduced are minimal, i.e. there are no smaller unused prameters of
    * the same type. */ 
  private def isCanonicalTransition(pre: Concretization, post: Concretization)
      : Boolean = {
    // iterate through pre and post, recording which parameters are used.
    val bitMap = 
      // FIXME: size below is a bit arbitrary
      Array.tabulate(numFamilies)(f => new Array[Boolean](remapSizes(f)))
    // Record the parameters in bitMap 
    @inline def recordIds(st: State) = {
      val ids = st.ids; val typeMap = st.typeMap
      for(i <- 0 until ids.length){
        val id = ids(i)
        if(!isDistinguished(id)) bitMap(typeMap(i))(id) = true
      }
    }
    @inline def recordIdsL(sts: List[State]) = for(st <- sts) recordIds(st)
    @inline def recordIdsA(sts: Array[State]) = for(st <- sts) recordIds(st)
    recordIdsL(pre.servers.servers); recordIdsA(pre.components)
    recordIdsL(post.servers.servers); recordIdsA(post.components)
    // Now iterate through, seeing which are missing
    var ok = true; var f = 0
    while(f < numTypes && ok){
      var i = 0; val size = typeSizes(f)
      while(i < size && bitMap(f)(i)) i += 1
      while(i < size && !bitMap(f)(i)) i += 1
      ok = i == size // true if there's a gap in typeSizes(f)
      f += 1
    }
    ok
  }

  /** Next states of st after performing e, synchronising with (f,id). */
  def nextsAfter(st: State, e: EventInt, f: Family, id: Identity)
      : Array[State] =
    components.getTransComponent(st).nexts(e, f, id)

}

// ==================================================================

// object System{

//   /** The System being checked.  Set by Checker. */
//   //private var system: System = null

//   //def setSystem(sys: System) = system = sys

//   /** Show event e. */
//   // def showEvent(e: EventInt) = system.showEvent(e)

// }
