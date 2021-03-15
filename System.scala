package ViewAbstraction.SystemP

import ViewAbstraction._
import ViewAbstraction.RemapperP.Remapper
import ViewAbstraction.CombinerP.Combiner
import uk.ac.ox.cs.fdr.{Option => _, _}
import scala.collection.JavaConverters._
import scala.collection.mutable.{Map,Stack,Set,ArrayBuffer,HashMap}
import ox.gavin.profiling.Profiler

/** An object that creates the System corresponding to the CSP file fname.
  * @param checkDeadlock are we checking for deadlock? */
class System(fname: String, checkDeadlock: Boolean, 
             significancePaths: List[SignificancePath]) {
  // type View = Views.View

  var verbose = false

  /** The parser of the annotations in the CSP file. */
  private val file: CSPFileParser =
    try{ new CSPFileParser(fname) }
    catch {
      case error: java.io.FileNotFoundException => println(error); sys.exit
      case error: InputFileError => println(error); sys.exit
      case error: FileLoadError => println(error); sys.exit
    }
 
  /** Object encapsulating the FDR session. */
  protected[SystemP] val fdrSession = new FDRSession(fname)

  /** Convert event represented by e to the String corresponding to the
    * script. */
  def showEvent(e: EventInt) = fdrSession.eventToString(e)

  // Set the number of visible events.  The visible events are numbered in
  // [3..fdrSession.numEvents+3), so we initialise arrays indexed by events to
  // size fdrSession.numEvents+3.
  numEvents = fdrSession.numEvents
  // println("numEvents = "+numEvents)
  eventsSize = numEvents+3

  fdrSession.initEvents(eventsSize)

  /** Names of symmetric subtypes, indexed by component family number. */
  familyTypeNames = file.identityTypes.toArray

  assert(familyTypeNames.length == numFamilies && 
           familyTypeNames.distinct.length == numTypes)

  familyNames = file.componentProcessNames.toArray

  /** Names of supertypes of symmetric subtypes, indexed by component
    * family number. */
  private val superTypeNames: Array[String] =
    familyTypeNames.map(fdrSession.getSuperType(_))

  /** The internal representation of each type inside FDR. */
  private val fdrTypeIds =
    Array.tabulate(numFamilies)(i => fdrSession.getTypeInt(familyTypeNames(i))) 

  /** Builder of transition systems. */
  private val transMapBuilder =
    new FDRTransitionMap(fdrSession, superTypeNames)

  println("Creating components")

  private val actives = file.componentActives.toArray

  private val activeFamilies = (0 until numFamilies).filter(actives(_))
  private val passiveFamilies = (0 until numFamilies).filter(!actives(_))
  println(s"Active families: $activeFamilies; passive families: $passiveFamilies")

  /** Model of the replicated components. */
  private val components = new Components(
    fdrSession, transMapBuilder, fdrTypeIds,
    familyNames, file.componentAlphabets.toArray, 
    file.componentRenames.toArray, actives)

  /** The size of each indexing subtype, by type number. */
  private val idSizes = typeSizes

  /** The size of each indexing subtype, by component family number. */
  private val indexingTypeSizes = 
    familyTypeNames.map(fdrSession.getTypeValues(_).length).toArray
  // println("indexingTypeSizes = "+indexingTypeSizes.mkString(", "))
  // IMPROVE: this repeats work in Components

  /** Alphabet of components: componentAlphaBitMaps(e) is true if e is in the
    * alphabet of the components. */
  private val componentAlphaBitMap = components.alphaBitMap 

  /** Is v a ComponentView for an active component? */
  def isActive(v: View) = v match{
    case cv: ComponentView => actives(cv.principal.family)
  }

  /** Model of the servers. */
  val servers =
    new Servers(file, fdrSession, transMapBuilder,
                components.getEventMap, indexingTypeSizes)

  /** Names of servers. */
  def serverNames = servers.serverNames

  /** Bit map for server alphabets: serverAlphaBitMap(e) is true if e is in the
    * servers' alphabet. */ 
  // private val serverAlphaBitMap = servers.alphaBitMap

  var threeWaySyncFound = false
  // Boolean array giving three-way syncs.  threeWaySyncs(f1)(f2) is true for
  // f1 >= f2 if there is a three-way synchronisation between families f1 and
  // f2.
  var threeWaySyncs: Array[Array[Boolean]] = null

  private def init() = {
    // Create the mapping from control states to types of parameters
    transMapBuilder.createStateTypeMap

    // Split transitions of components, based on which processes they
    // synchronise with.
    components.categoriseTrans(servers.alphaBitMap)

    scriptNames = transMapBuilder.getNameMap

    val cptEventMap: Array[List[ProcessIdentity]] = 
      components.getEventMap
    val serverAlphaMap: Array[Boolean] = servers.alphaBitMap

    // find three-way synchronisations
    assert(cptEventMap.length == eventsSize, 
           s"${cptEventMap.length}; $numEvents")
    assert(serverAlphaMap.length == eventsSize, 
           s"${serverAlphaMap.length}; $numEvents; ${showEvent(numEvents+2)}")
    var e = 3
    threeWaySyncs = Array.tabulate(numFamilies)(f => new Array[Boolean](f+1))
    while(e < eventsSize){
      if(cptEventMap(e).length == 2 && serverAlphaMap(e)){
        val family1 = cptEventMap(e)(0)._1; val family2 = cptEventMap(e)(1)._1
        if(false)
          println("Three-way synchronisation on event "+showEvent(e)+"\n"+
                    "families "+family1+" and "+family2)
        threeWaySyncFound = true
        threeWaySyncs(family1 max family2)(family1 min family2) = true
      }
      e += 1
    } // end of while
    for(f1 <- 0 until numFamilies; f2 <- 0 to f1; if threeWaySyncs(f1)(f2))
      println(s"Three-way synchronisation involving families $f2 and $f1")

    fdr.libraryExit()
  }

  init()

  /** Representation of the tau event. */
  // private val Tau = 1

  /** Representation of the event error. */
  val Error = fdrSession.eventToInt("error")

  /** Finaliser.  Should be called on exit. */
  def finalise = fdr.libraryExit()

  // At end of construction, close FDR.
  finalise

  /** The initial system views. */
  def initViews: (ViewSet, Array[View]) = {
    // val k = aShapes.head.sum
    // println("initViews "+k+"; "+aShapes.map(_.mkString("<", ",", ">")))
    val serverInits: List[State] = servers.inits
    val viewSet = ViewSet(); val activeViews = new ArrayBuffer[View]
    // All views 
    val views = components.initViews(ServerStates(serverInits))
    // println("views = \n  "+views.map(_.toString).mkString("\n  "))
    // println("#views = "+views.length)
    // assert(cptViews.forall(_.length == k))
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
    // println(s"Transitions for ${(pf,pi)}")
    val serverTrans: servers.ServerTransitions = 
      servers.transitions(cv.servers.servers)

    // IMPROVE: the transitions probably aren't in the best form
    val conc0 = Concretization(cv)
    val activePrincipal = isActive(cv) // is the principal active

    // Case 1: events of the principal component with no synchronisation
    if(activePrincipal) 
      for(i <- 0 until princTrans.eventsSolo.length-1;
        st1 <- princTrans.nextsSolo(i)){
        val post = Concretization(cv.servers, st1, cv.others)
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
              if(!activePrincipal) println("server-only event: "+showEvent(sE))
              // println(s"Server-principal sync on ${showEvent(pE)}")
              for(pNext <- pNexts(cptIndex); sNext <- sNexts(serverIndex)){
                val post = Concretization(ServerStates(sNext), pNext, cv.others)
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
      val theseTrans = princTrans.transComponent(f)(id)
      val componentIx = // index of (f,id) in others, or -1
        cv.others.indexWhere(_.componentProcessIdentity == (f,id))
      if(theseTrans != null){ 
        val (oEs, oNs): (ArrayBuffer[EventInt], ArrayBuffer[List[State]]) = 
          theseTrans
        // Find id of relevant component; find compatible states of that
        // component.
        for(i <- 0 until oEs.length-1){
          val e = oEs(i); assert(i < Sentinel)
          assert(components.passiveCptsOfEvent(e) == List((f,id)))
          if(componentIx >= 0){ // the passive component is present
            val passiveSt = cv.others(componentIx) 
            // Next states for the present passives
            val pNexts = components.getTransComponent(passiveSt).nexts(e, pf, pi)
            for(pNext <- pNexts){
              // Post-state of others: insert pNext into cv.others
              val othersPost = cv.others.clone; othersPost(componentIx) = pNext
              for(st1 <- oNs(i)){
                val post = Concretization(cv.servers, st1, othersPost)
                maybeAdd(conc0, e, post, null)
              }
            }
          }
          else{ // the passive component is absent
            val conc0 = Concretization(cv)
            for(st1 <- oNs(i)){ // the post state of the principal cpt
              val post = Concretization(cv.servers, st1, cv.others)
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
        val post = 
          Concretization(ServerStates(newServers), cv.principal, cv.others)
        maybeAdd(conc0, e, post, null)
      }
      // println("sEsSolo = "+sEsSolo.init.map(showEvent).mkString("; "))
      index += 1; e = sEsSolo(index)
    }

    // Case 5: events between server, principal component and one other
    // component. 
    val cptTrans2 = princTrans.transServerComponent
    for(of <- passiveFamilies; oi <- 0 until idSizes(of)){
      // Synchronisations between principal, other component (of,oi) and
      // server, from principal's state, and then from server's state.
      val theseCptTrans: (ArrayBuffer[EventInt], ArrayBuffer[List[State]]) =
        cptTrans2(of)(oi)
      val theseServerTrans
          : (ArrayBuffer[EventInt], ArrayBuffer[List[List[State]]]) =
        serverTrans.transSync2((pf,pi), (of,oi))
      if(theseCptTrans != null && theseServerTrans != null){
        val (pEs,pNexts) = theseCptTrans; val (sEs, sNexts) = theseServerTrans
        // is the other component in cv?
        val otherIndices = (0 until cv.others.length).filter(i =>
          cv.others(i).componentProcessIdentity == (of,oi))
        // val otherPresent = 
        //   cv.others.exists(_.componentProcessIdentity == (of,oi))
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
                val otherState = cv.others(otherIndex)
                // Synchronisations between otherState and the principal
                val otherNexts
                    : (ArrayBuffer[EventInt], ArrayBuffer[List[State]]) =
                  components.getTransComponent(otherState).
                    transServerComponent(pf)(pi)
                if(otherNexts != null){
                  val (otherEs, otherStates) = otherNexts
                  var oj = 0;  while(otherEs(oj) < pE) oj += 1
                  if(otherEs(oj) == pE){
                    val pre = Concretization(cv)
                    // Possible next states of others
                    val newOtherss = otherStates(oj).map{ st => 
                      val nos = cv.others.clone; nos(otherIndex) = st; nos }
                    for(newServers <- sNexts(sj); newPrincSt <- pNexts(pj);
                      newOthers <- newOtherss){
                      val post = Concretization(ServerStates(newServers), 
                        newPrincSt, newOthers)
                      if(verbose)
                        println(s"Three-way synchronisation: "+
                          s"$pre -${showEvent(sE)}-> $post "+
                          "with present other ${(of,oi)}")
                      maybeAdd(pre, sE, post, null)
                    }
                  }
                }
              } // end of otherIndices.nonEmpty
              else{
                val pre = Concretization(cv)
                for(newServers <- sNexts(sj); newPrincSt <- pNexts(pj)){
                  val post = Concretization(ServerStates(newServers), 
                    newPrincSt, cv.others)
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
      Array.tabulate(numFamilies)(f => new Array[Boolean](typeSizes(f)))
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

  // private val consistentStatesCache = 
  //   new HashMap[(ProcessIdentity, Concretization, EventInt, ComponentView),
  //     ArrayBuffer[(State, List[State])] ]()

  // IMPROVE: store mapping from (pre, pid, st1) to the maps that map st1's
  // identity to pid.  Avoid recalculating.


  /** Get all renamings of cv that: (1) include a component with identity pid;
    * (2) agree with pre on the states of all common components; and (3) can
    * perform e with pre.principal if e >= 0.
    * @return the renaming of the component with identity pid, and all
    * post-states of that component optionally after oe.  */
  def consistentStates(pre: Concretization, pid: ProcessIdentity, 
    e: EventInt, cv: ComponentView)
      : ArrayBuffer[(State, List[State])] = {
    val buffer = new ArrayBuffer[(State, List[State])]()
    val (f,id) = pid; val servers = pre.servers; require(cv.servers == servers)
    val preCpts = pre.components; val cpts = cv.components
    val serverRefs = id < servers.numParams(f) // do servers reference pid?
    val (fp, idp) = preCpts(0).componentProcessIdentity// id of principal of pre
    //println(s"consistentStates(${State.showProcessId(pid)}, $pre, $cv)")
    // Find all components of cv that can be renamed to a state of pid
    // that can perform e.
    for(i <- 0 until cpts.length){ 
      val st1 = cpts(i)
      // Profiler.count(pre.toString+pid+cv)
      // Try to make st1 the component that gets renamed.  Need st1 of family
      // f, and its identity either equal to id, or neither of those
      // identities in the server identities (so the renaming doesn't change
      // servers).
      if(st1.family == f && 
        (st1.id == id || !serverRefs && st1.id >= servers.numParams(f))){
        // Calculate (in maps) all ways of remapping st1 (consistent with the
        // servers) so that: (1) its identity maps to id; (2) other parameters
        // are injectively mapped either to a parameter in pre.components,
        // but not the servers; or the next fresh parameter.
        val map0 = servers.remappingMap 
        val (otherArgs, nextArg) = Remapper.createMaps1(servers, preCpts)
        otherArgs(f) = otherArgs(f).filter(_ != id)
        nextArg(f) = nextArg(f) max (id+1)
        val maps = Combiner.remapToId(map0, otherArgs, nextArg, cpts, i, id)
        for(map <- maps){
          val renamedState = Remapper.applyRemappingToState(map, st1)
          if(!renamedState.representableInScript){
            println("Not enough identities in script to make\n"+
              s"$pre and\n$cv consistent.\n"+
              s"Renaming of $st1 gives ${renamedState.toString0}")
            sys.exit
          }
          // should have renamedState.ids in ran map.  IMPROVE: assertion only
          val ids1 = renamedState.ids; val typeMap = renamedState.typeMap
          var j = 0
          while(j < ids1.length){
            assert( ids1(j) < 0 || map(typeMap(j)).contains(ids1(j)) ,
              "\nmap = "+Remapper.show(map)+"undefined on = "+renamedState)
            j += 1
          }
          val nexts = (
            if(e >= 0) 
              components.getTransComponent(renamedState).nexts(e, fp, idp)
            else List(renamedState)
          )
          if(nexts.nonEmpty && !buffer.contains((renamedState, nexts))){
            if(checkCompatible(
              map, renamedState, cpts, i, preCpts, otherArgs))
              buffer += ((renamedState, nexts))
          }
          // if(View.agreesWithCommonComponent(renamedState, preCpts)){
          //   // Renamed state consistent with preCpts
          //   // Test whether e is possible, and get next states
          //   val nexts = (
          //     if(e >= 0) 
          //       components.getTransComponent(renamedState).nexts(e, fp, idp)
          //     else List(renamedState)
          //   )
          //   if(nexts.nonEmpty && !buffer.contains((renamedState, nexts))){
          //     // Check a corresponding renaming of the rest of cpts agrees
          //     // with cpts on common components.  Trivially true if singleton
          //     val otherArgs1 = Remapper.removeParamsOf(otherArgs, renamedState)
          //     if(Combiner.areUnifiable(cpts, preCpts, map, i, otherArgs1)){
          //       if(false) println((renamedState, nexts.mkString("[",",","]")))
          //       buffer += ((renamedState, nexts))
          //     }
          //   } // end of if(nexts.nonEmpty && !buffer.contains(...))
          // } // end of else (Renamed state consistent with preCpts)
        } // end of for(map <- maps)
      }
    } // end of for(i <- ...)
    buffer
  } // end of consistentStates


  private def checkCompatible(
    map: RemappingMap, renamedState: State, cpts: Array[State], i: Int,
    preCpts: Array[State], otherArgs: OtherArgMap): Boolean
  = {
    // val (fp, idp) = preCpts(0).componentProcessIdentity
    if(View.agreesWithCommonComponent(renamedState, preCpts)){
      // Renamed state consistent with preCpts
      // Test whether e is possible, and get next states
      // val nexts = (
      //   if(e >= 0) components.getTransComponent(renamedState).nexts(e, fp, idp)
      //   else List(renamedState)
      // )
      // if(nexts.nonEmpty && !buffer.contains((renamedState, nexts))){
        // Check a corresponding renaming of the rest of cpts agrees
        // with cpts on common components.  Trivially true if singleton
        val otherArgs1 = Remapper.removeParamsOf(otherArgs, renamedState)
        if(Combiner.areUnifiable(cpts, preCpts, map, i, otherArgs1)){
          // if(false) println((renamedState, nexts.mkString("[",",","]")))
          true // buffer += ((renamedState, nexts))
        }
        else false
      //} // end of if(nexts.nonEmpty && !buffer.contains(...))
    } // end of else (Renamed state consistent with preCpts)
    else false
  }



}
