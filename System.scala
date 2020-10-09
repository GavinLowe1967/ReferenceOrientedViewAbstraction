package ViewAbstraction

import uk.ac.ox.cs.fdr.{Option => _, _}
import scala.collection.JavaConverters._
import scala.collection.mutable.{Map,Stack,Set,ArrayBuffer}
import ox.gavin.profiling.Profiler

/** An object that creates the System corresponding to the CSP file fname.
  * @param checkDeadlock are we checking for deadlock? */
class System(fname: String, checkDeadlock: Boolean, 
             significancePaths: List[SignificancePath]) {
  // type View = Views.View

  /** The parser of the annotations in the CSP file. */
  private val file: CSPFileParser =
    try{ new CSPFileParser(fname) }
    catch {
      case error: java.io.FileNotFoundException => println(error); sys.exit
      case error: InputFileError => println(error); sys.exit
      case error: FileLoadError => println(error); sys.exit
    }
 
  /** Object encapsulating the FDR session. */
  private val fdrSession = new FDRSession(fname)

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
    // BitPackedSubSystemView.init(State.stateCount)
  }

  init()

  /** Representation of the tau event. */
  // private val Tau = 1

  /** Representation of the event error. */
  private val Error = fdrSession.eventToInt("error")

  /** Finaliser.  Should be called on exit. */
  def finalise = fdr.libraryExit()

  // At end of construction, close FDR.
  finalise

  /** The shapes of concretizations. */
  // private var cShapes: List[Array[Int]] = null
  // def setCShapes(cs: List[Array[Int]]) = cShapes = cs

  // ============================== Main functions called while checking

  /** Companion object of the relevant subclass of View. */
  // val viewCompanion = View

  /** The initial system views. */
  def initViews: (ViewSet, Array[View]) = {
    // val k = aShapes.head.sum
    // println("initViews "+k+"; "+aShapes.map(_.mkString("<", ",", ">")))
    val serverInits: List[State] = servers.inits
    val viewSet = ViewSet(); val activeViews = new ArrayBuffer[View]
    // All views 
    val views = components.initViews(new ServerStates(serverInits))
    // println("views = \n  "+views.map(_.toString).mkString("\n  "))
    println("#views = "+views.length)
    // assert(cptViews.forall(_.length == k))
    for(v <- views){
      val v1 = Remapper.remapView(v)
      println(v.toString+" -> "+v1.toString+(if(isActive(v)) "*" else ""))
      if(viewSet.add(v1)){
        if(isActive(v1)) activeViews += v1
        println("**") 
      }
    }
      // val sv = View.mkView(serverInits, vs)
      // if(!sysViews.add(sv)) View.returnView(sv)
      // Views.returnView(vs)
    (viewSet, activeViews.toArray)
  }
  
  /** Calculate all views of concs, and
    * add them to absViews. */
  def alpha(concs: ArrayBuffer[Concretization], views: ViewSet)
      : ArrayBuffer[View] = {
    val ab = new ArrayBuffer[View]
    for(conc <- concs; v <- View.alpha(conc)){ views.add(v); ab += v }
    ab
  }
  //  View.alpha(aShapes, concViews, absViews, ply)

  /** We represent sets of transitions corresponding to a ComponentView cv using
    * lists of tuples of type TransitionRep.  Each tuple (pre, e, post, pids)
    * represents concrete transitions pre U new U cpts -e-> post U new' U
    * cpts, for each set new and new', cpts such that: (1) new, new' have
    * component identities pIds and transition new -e-> new'; (2) the three
    * parts have disjoint identities.  The concretizations pre and post
    * contain the same component identities, namely those identities in cv.
    */
  type TransitionRep = 
    (Concretization, EventInt, Concretization, List[ProcessIdentity])

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
        pids: List[ProcessIdentity]) =
      if(isCanonicalTransition(pre, post)) result ::= ((pre, e, post, pids)) 
      else println(s"Not cannonical $pre -${showEvent(e)}-> $post")

    val princTrans = components.getTransComponent(cv.principal)
    val (pf,pi) = cv.principal.componentProcessIdentity
    // println(s"Transitions for ${(pf,pi)}")
    val serverTrans: servers.ServerTransitions = 
      servers.transitions(cv.servers.servers)

    // IMPROVE: the transitions probably aren't in the best form

    // Case 1: events of the principal component with no synchronisation
    val conc0 = Concretization(cv)
    for(i <- 0 until princTrans.eventsSolo.length-1; 
        st1 <- princTrans.nextsSolo(i)){
      val post = Concretization(cv.servers, st1, cv.others)
      // result ::= ((conc0, princTrans.eventsSolo(i), post, List()))
      maybeAdd(conc0, princTrans.eventsSolo(i), post, List())
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
            // println(s"Server-principal sync on ${showEvent(pE)}")
            for(pNext <- pNexts(cptIndex); sNext <- sNexts(serverIndex)){
              val post = Concretization(ServerStates(sNext), pNext, cv.others)
              maybeAdd(conc0, sE, post, List())
            }
            serverIndex += 1; sE = sEs(serverIndex)
            cptIndex += 1; pE = pEs(cptIndex)
          }
        }
      }
    }

    // Case 3: events synchronising principal component and one component.
    for(f <- passiveFamilies; i <- 0 until idSizes(f)){
      val theseTrans = princTrans.transComponent(f)(i)
      if(theseTrans != null){ 
        val (oEs, oNs): (ArrayBuffer[EventInt], ArrayBuffer[List[State]]) = 
          theseTrans
        // Find id of relevant component; find compatible states of that
        // component.
        for(i <- 0 until oEs.length-1){
          val e = oEs(i); assert(i < Sentinel)
          // Ids of passive components involved in this synchronisation.
          val passives = components.passiveCptsOfEvent(e)
          assert(passives.length == 1) // IMPROVE (simplifying assumption).
          // Other components of cv in this synchronisation
          val presentIndices = (0 until cv.others.length).filter(i =>
            passives.contains(cv.others(i).componentProcessIdentity))
          // val presentPassives = presentIndices.map(i => cv.others(i))
          // val presentPassives1 = cv.others.filter(st => 
          //   passives.contains(st.componentProcessIdentity))
          // assert(presentPassives sameElements presentPassives1) // IMPROVE
          // Ids of components in the synchronisation but not in cv
          val absentPassives = passives.filterNot( pId => 
            cv.others.exists(_.componentProcessIdentity == pId) )
          if(presentIndices.nonEmpty){
            assert(absentPassives.isEmpty) // IMPROVE (simplifying assumption)
            val passiveIx = presentIndices.head
            val passiveSt = cv.others(passiveIx) // presentPassives.head
            // Next states for the present passives
            val pNexts = components.getTransComponent(passiveSt).nexts(e, pf, pi)
            println(s"Searching for synchronisations with $passiveSt on "+
              showEvent(e)+": "+pNexts)
            for(pNext <- pNexts){
              // NOTE: not tested for pNext != passiveSt
              // Post-state of others: insert pNext into cv.others
              val othersPost = cv.others.clone; othersPost(passiveIx) = pNext
              for(st1 <- oNs(i)){
                val post = Concretization(cv.servers, st1, othersPost)
                // println(post)
                maybeAdd(conc0, e, post, List())
              }
            }
          }
          else{
            val cPid = absentPassives.head // the absent component
            val conc0 = Concretization(cv)
            for(st1 <- oNs(i)){ // the post state of the principal cpt
              val post = Concretization(cv.servers, st1, cv.others)
              maybeAdd(conc0, e, post, List(cPid))
            }
          }

        }

        // ???
      }
      // FIXME
    }

    // FIXME: other cases

    // for((pre, e, post) <- result) println(s"$pre -${showEvent(e)}-> $post")
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

  /** Get all renamings of cv1 that: (1) include a component with identity pid;
    * (2) agree with conc on the states of all common components; and (3) if
    * oe = Some(e) can perform e with conc.principal. 
    * @return the renaming of the component with pid, and all post-states of that
    * component optionally after oe.  */
  def consistentStates(pid: ProcessIdentity, conc: Concretization, 
    oe: Option[EventInt], cv1: ComponentView)
      : ArrayBuffer[(State, List[State])] = {
    val buffer = new ArrayBuffer[(State, List[State])]()
    val (f,id) = pid; val servers = conc.servers; require(cv1.servers == servers)
    val cpts = conc.components; val cpts1 = cv1.components
    val (fp, idp) = cpts(0).componentProcessIdentity
    // println(s"consistentStates($pid, $conc, $cv1)")
    // println(s"consistentStates(${State.showProcessId(pid)}, $cv)\n"+
    //   s"  with $cv1")
    // Find all components of cv1 that can be renamed to a state of pid
    // that can perform e.
    for(i <- 0 until cpts1.length){
      val st1 = cpts1(i)
      // Need st1 of family f, and its identity either not in the server
      // identities, or equal to id (so the renaming doesn't change servers).
      if(st1.family == f && (st1.id == id || st1.id >= servers.numParams(f))){
        // All ways of remapping st1 (consistent with the servers) so that:
        // (1) its identity maps to id; (2) other parameters are injectively
        // mapped either to a parameter in cv, or the next fresh parameter.
        // Create appropriate maps.
        val map0 = Remapper.createMap(servers.rhoS)  // newRemappingMap
        val (otherArgs, nextArg) = Remapper.createMaps1(servers, cpts)
        otherArgs(f) = otherArgs(f).filter(_ != id)
        nextArg(f) = nextArg(f) max (id+1)
        // println(s"Remapping $st1")
        val maps = Remapper.remapToId(map0, otherArgs, nextArg, cpts1, i, id)
        for(map <- maps){
          val renamedState = Remapper.applyRemappingToState(map, st1)
          // println(s"map = ${Remapper.showRemappingMap(map)}; "+
          //   s"renamedState = $renamedState}")
          // Test whether e is possible, and get next states
          val nexts = oe match{
            case Some(e) =>
              components.getTransComponent(renamedState).nexts(e, fp, idp)
            case None => List(renamedState) 
          }
          // println(s"nexts = $nexts")
          if(nexts.nonEmpty){   
            // println(s"Remapping $st1")
            // IMPROVE: this can be simplified if cpts1 is a singleton.
            // NOTE: hasn't been tested for cpts1 not a singleton.
            // Extend map to the rest of cpts1, and obtain corresponding
            // renamed components.
            val rnTypeMap = renamedState.typeMap; val rnIds = renamedState.ids
            // otherArgs with args of renamedState removed
            val otherArgs1: Remapper.OtherArgMap =
              Array.tabulate(numFamilies)(f => otherArgs(f))
            for(j <- 0 until rnIds.length){
              val f1 = rnTypeMap(j)
              otherArgs1(f) = otherArgs1(f).filter(_ != rnIds(j))
            }
            for(renamedCpts <- Remapper.remapRest(map, otherArgs1, cpts1, i)){
              // println(s"renamedCpts = "+renamedCpts.mkString("[",",","]"))
              // check that it is consistent with cpts on common components.
              var i1 = 0; var ok = true
              while(i1 < renamedCpts.length && ok){
                val rnCpt = renamedCpts(i1)
                val rnCptId = rnCpt.componentProcessIdentity; var j = 0
                while(j < cpts.length && ok){
                  val cptj = cpts(j)
                  if(cptj.componentProcessIdentity == rnCptId){
                    ok = rnCpt == cptj
                    // println(s"Comparing $rnCpt and $cptj: $ok")
                  }
                  j += 1
                }
                i1 += 1
              } // end of outer while
              if(ok) buffer += ((renamedState, nexts))
            } // end of for(renamedCpts <- ...)
          }
        } // end of for(map <- maps)
      }
    } // end of for(i <- ...)
    buffer
  } // end of consistentStates


}


// =======================================================
// =======================================================
// dead code below here



  /** Check that there are enough values of each type to capture all the
    * Views in svs. */
  // def checkTypeSizes(svs: Array[View]) = {
  //   for(sv <- svs){
  //     // sv.checkInvariant
  //     val numParams = sv.numParams
  //     for(i <- 0 until numTypes; if(numParams(i) > idSizes(i))){
  //       println("Not enough identities of type "+typeNames(i)+" in script ("+
  //                 idSizes(i)+") to represent system view\n"+sv.toString0)
  //       sys.exit
  //     }
  //   }
  // }

  // /** Check that there are enough values of each type to capture sv. */
  // def checkTypeSizes(sv: View) = {
  //   // sv.checkInvariant
  //   val numParams = sv.numParams
  //   for(i <- 0 until numTypes; if(numParams(i) > idSizes(i))) synchronized{
  //     println("Not enough identities of type "+typeNames(i)+" in script ("+
  //               idSizes(i)+") to represent system view\n"+sv.toString0)
  //     sys.exit
  //   }
  // }

  /** Is the system view sv significant according to significancePaths? */
  // private def significant(sv: View): Boolean = { ??? }
  //   // Check sv is significant according to sp
  //   def significant1(sp: SignificancePath): Boolean = {
  //     // assert(sp.length >= 1)
  //     val componentsA = sv.componentView
  //     val components = componentsA.toList; Views.returnView(componentsA)
  //     // Next family, and its indexing type.
  //     var f = sp(0); val t = indexingTypes(f)
  //     // Identities of family f to check present
  //     var ids =  sv.serverIds(t)
  //     // Have any identities been found to be missing, making sv not
  //     // significant?
  //     var missingId = false
  //     // Those families for which identities were missing
  //     var missingFamilies = List[Family]()
  //     // Components that are "spare", in the sense that they have not
  //     // been necessary to show the significance of sv.
  //     var spare = components
  //     var sp1 = sp // .tail // remainder of sp

  //     // Check every identity in ids of family f = sp1.head is present
  //     // in sv; and continue.
  //     while(sp1.nonEmpty){
  //       // Processes of current family
  //       val fProcs = components.filter(_.family == f)
  //       // Identities of family f in sv
  //       val fIds = fProcs.map(_.ids.head)
  //       // Check whether ids is a subset of fIds
  //       if(!ids.forall(id => fIds.contains(id))){
  //         missingId = true; missingFamilies ::= f
  //       }
  //       // Update spare: remove those of family f with identity in ids
  //       spare = spare.filter(st => st.family != f || !ids.contains(st.ids.head))
  //       sp1 = sp1.tail
  //       if(sp1.nonEmpty){
  //         // Next family and its indexing type
  //         f = sp1.head; assert(f != -1); val t = indexingTypes(f)
  //         // Identities of type t referenced by fProcs
  //         ids = (for(st <- fProcs; i <- 0 until st.ids.length;
  //                    if State.stateTypeMap(st.cs)(i) == t)
  //                yield st.ids(i) ).distinct
  //       }
  //     }

  //     if(missingId)
  //       // Check whether this was not significant because views are not
  //       // large enough.
  //       checkLargeEnough(sv, sp, components, spare, missingFamilies)
  //     !missingId
  //   } // end of significant1

  //   significancePaths.forall(significant1)
  // }

  /** Are concretizations large enough to capture components, with spare
    * removed, plus each element of missingFamilies added?  If not,
    * give an error and exit. */
  // @inline private def checkLargeEnough(
  //   sv: View, sp: SignificancePath, 
  //   components: List[State], spare: List[State], missingFamilies: List[Family])
  //   = { ??? }
    // // shape of sv ...
    // val thisShape = new Array[Int](numFamilies)
    // for(st <- components) thisShape(st.family) += 1
    // // ... less the spare states ...
    // for(st <- spare) thisShape(st.family) -= 1
    // for(f <- missingFamilies.distinct){
    //   // ... plus each missing family
    //   thisShape(f) += 1 // (*)
    //   // test if it's included in a member of cShapes
    //   if(!cShapes.exists(shape =>
    //        (0 until numFamilies).forall(f1 => thisShape(f1) <= shape(f1)))){
    //     println("Concretizations are not large enough to include the "+
    //               "significant extension of ")
    //     println(s"$sv,")
    //     println("adding a state of family "+f+
    //               ", corresponding to significance path "+sp)
    //     sys.exit
    //   }
    //   thisShape(f) -= 1 // undo (*)
    // }


  /** Count of new concretizations found by post on this ply. */
  //private val postCount = new java.util.concurrent.atomic.AtomicInteger

  /** Sets of Views are passed around using the following type. */
  // private type SVBuffer = ArrayBuffer[View]

  /** New version of post, calculating the post image from sysViews.
    * @param sysConcViews the set of system views seen so far.  
    * @return (1) An array holding the new post-states; (2) the list of states
    * from which error is possible; (3) the list of deadlocked states. */
  // def post(sysViews: ArrayBuffer[View], sysConcViews: ViewSet)
  //     : (SVBuffer, SVBuffer, SVBuffer) = {
  //   val posts = new SVBuffer // the post-image
  //   val postsSVS = // Views seen on this call to post, if memoryless
  //     if(memoryless) new SeqViewSet else null   
  //   val errors = new SVBuffer; val deadlocks = new SVBuffer
  //   for(sv <- sysViews) 
  //     post1(sv, sysConcViews, errors, deadlocks, posts, postsSVS)
  //   (posts, errors, deadlocks)
  // }

  /** Calculate the post-image of sv, and add to posts; add error states and
    * deadlock states to errors and deadlocks, respectively.
    * @param sysConcViews the set of system views seen so far.
    * @param posts SVBuffer holding the posts found on this ply.
    * @param thisPly posts found on this ply: if memoryless, this is used to 
    * remove repeats.  */
  // @inline private def post1(
  //   sv: View, sysConcViews: ViewSet, errors: SVBuffer,
  //   deadlocks: SVBuffer, posts: SVBuffer, thisPly: ViewSet) = { ??? }
    // assert((thisPly != null) == memoryless)
    // var deadlock = true // Has no transition from this state been found?
    // val sStates = sv.servers; val cptView: View = sv.componentView
    // val l = cptView.length
    // // Process identities for components
    // val cptIds: Array[Parameter] = cptView.map(_.componentProcessIdentity)
    // val serverTrans: servers.ServerTransitions = servers.transitions(sStates)
    // val cptTrans: Array[components.ComponentTransitions] =
    //   cptView.map(components.getTransComponent)

    // // Record the transition from sv with event e to (ss,v).
    // @inline def addTrans(e: EventInt, ss: List[State], v: View) = {
    //   // assert(v.length == l, Views.show(v)+" "+l)
    //   deadlock = false
    //   val sv1 = View.mkView(ss, v) // don't recycle v here
    //   // if(verbose) println(sv+" -"+showEvent(e)+"->\n  "+sv1)
    //   if(e == Error) synchronized{ errors += sv }
    //     // The order below ensures that we add to thisPly only if sv1 is a new
    //     // View
    //   if(sysConcViews.add(sv1)){
    //     if(!memoryless || thisPly.add(sv1)){ 
    //       if(debuggable) sv1.setPred(sv, e)
    //       posts += sv1  // IMPROVE: seems unnecessary if memoryless
    //     }
    //     else{
    //       // If we get here, sv1 has been double-counted within the tally of
    //       // Views in sysConcViews.  IMPROVE
    //       // assert(memoryless)
    //       sysConcViews.addCount(-1)
    //       View.returnView(sv1)
    //     }
    //   }
    //   else View.returnView(sv1)
    // }

    // // Case 1: events of only the servers
    // val sEventsSolo = serverTrans.eventsSolo
    // val sNextsSolo = serverTrans.nextsSolo
    // var i = 0; var e = sEventsSolo(0) // inv: e = sEventsSolo(i)
    // while(e < Sentinel){
    //   val sss = sNextsSolo(i); var j = 0
    //   while(j < sss.length){ addTrans(e, sss(j), cptView); j += 1 }
    //   // don't recycle cptView!
    //   i += 1; e = sEventsSolo(i)
    // }

    // // Case 2: Synchronization between servers and one component
    // val sTransSync = serverTrans.transSync
    // for(j <- 0 until l){
    //   // Transitions of jth component, with process identity (f,id)
    //   val (f,id) = cptIds(j)
    //   val sTrans0 = sTransSync(f)(id) // corresponding server transitions
    //   if(sTrans0 != null){
    //     val (sEs, sNexts) = sTrans0 // transitions of servers
    //     // transitions of cpts
    //     val cTrans1: components.ComponentTransitions = cptTrans(j)
    //     val cEs = cTrans1.eventsServer; val cNexts = cTrans1.nextsServer
    //     var serverIndex = 0; var cptIndex = 0 // indexes for servers, cpt
    //     var sE = sEs(0); var cE = cEs(0) // next events of servers, cpt
    //     // inv: sE = sEs(serverIndex); cE = cEs(cptIndex)
    //     while(sE < Sentinel && cE < Sentinel){
    //       while(sE < cE){ serverIndex += 1; sE = sEs(serverIndex) }
    //       if(sE < Sentinel){
    //         while(cE < sE){ cptIndex += 1; cE = cEs(cptIndex) }
    //         if(sE == cE){ // can synchronise
    //           val sNexts0 = sNexts(serverIndex) // next states of servers
    //           for(cNext <- cNexts(cptIndex)){
    //             val newView = Views.insert(cptView, j, cNext)
    //             for(sNext <- sNexts0) addTrans(sE, sNext, newView)
    //             Views.returnView(newView) // recycle
    //           }
    //           serverIndex += 1; sE = sEs(serverIndex)
    //           cptIndex += 1; cE = cEs(cptIndex)
    //         }
    //       }
    //     } // end of while (sE < Sentinel && cE < Sentinel)
    //   }
    // }

    // // Case 3: Single component (not the server)
    // for(j <- 0 until l){
    //   // Transitions of jth component
    //   val trans1: components.ComponentTransitions = cptTrans(j)
    //   val es = trans1.eventsSolo; val nexts = trans1.nextsSolo
    //   var i = 0; var e = es(0) // inv: e = es(i)
    //   while(e < Sentinel){
    //     for(st1 <- nexts(i)){
    //       val newView = Views.insert(cptView, j, st1)
    //       addTrans(e, sStates, newView)
    //       Views.returnView(newView) // recycle
    //     }
    //     i += 1; e = es(i)
    //   }
    // }

    // // Case 4: Two components, but not the server
    // for(j1 <- 0 until l-1){
    //   // Transitions of j1th component with process identity (f1,id1)
    //   val (f1,id1) = cptIds(j1)
    //   val syncTrans1 = cptTrans(j1).transComponent
    //   for(j2 <- j1+1 until l){
    //     val (f2,id2) = cptIds(j2)
    //     val cptTrans1 = syncTrans1(f2)(id2) // tran's of (f1,id1) with (f2,id2)
    //     if(cptTrans1 != null){
    //       // tran's of (f2,id2) with (f1,id1)
    //       val cptTrans2 = cptTrans(j2).transComponent(f1)(id1)
    //       if(cptTrans2 != null){ // possibility of synchronisation
    //         val (es1,nexts1) = cptTrans1; val (es2,nexts2) = cptTrans2
    //         var index1 = 0; var e1 = es1(0); var index2 = 0; var e2 = es2(0)
    //         // Inv: e1 = es1(index1) && e2 = es2(index2)
    //         while(e1 < Sentinel && e2 < Sentinel){
    //           while(e1 < e2){ index1 += 1; e1 = es1(index1) }
    //           if(e1 < Sentinel){
    //             while(e2 < e1){ index2 += 1; e2 = es2(index2) }
    //             if(e1 == e2){ // can synchronise
    //               val theNexts1 = nexts1(index1)
    //               val theNexts2 = nexts2(index2)
    //               val newViews =
    //                 Views.insert2States(cptView, j1, theNexts1, j2, theNexts2)
    //               for(newView <- newViews){
    //                 addTrans(e1, sStates, newView)
    //                 Views.returnView(newView) // recycle
    //               }
    //               index1 += 1; e1 = es1(index1); index2 += 1; e2 = es2(index2)
    //             }
    //           }
    //         } // end of while(e1 < Sentinel && e2 < Sentinel)
    //       }
    //     }
    //   } // end of inner for
    // } // end of outer for; end of Case 4

    // // Case 5: Two components and the server
    // // Improve: avoid this if there are no three-way syncs
    // for(j1 <- 0 until l-1){
    //   // Three-way transitions of j1th component with process identity (f1,id1)
    //   val (f1,id1) = cptIds(j1)
    //   val syncTrans1 = cptTrans(j1).transServerComponent
    //   for(j2 <- j1+1 until l){
    //     val (f2,id2) = cptIds(j2)
    //     val cptTrans1 = syncTrans1(f2)(id2) // tran's of (f1,id1) with (f2,id2)
    //     if(cptTrans1 != null){
    //       // tran's of (f2,id2) with (f1,id1)
    //       val cptTrans2 = cptTrans(j2).transServerComponent(f1)(id1)
    //       if(cptTrans2 != null){
    //         val syncServerTrans = serverTrans.transSync2((f1,id1), (f2,id2))
    //         if(syncServerTrans != null){ // possibility of synchronisation
    //           val (esc1,nextsc1) = cptTrans1; val (esc2,nextsc2) = cptTrans2
    //           val (esS, nextsS) = syncServerTrans
    //           var index1 = 0; var e1 = esc1(0)
    //           var index2 = 0; var e2 = esc2(0)
    //           var indexS = 0; var eS = esS(0)
    //           // Inv: e1 = esc1(index1) && e2 = esc2(index2) &&
    //           // eS = esS(indexS)
    //           while(e1 < Sentinel && e2 < Sentinel && eS < Sentinel){
    //             while(e1 < (e2 max eS)){ index1 += 1; e1 = esc1(index1) }
    //             if(e1 < Sentinel){
    //               while(e2 < e1){ index2 += 1; e2 = esc2(index2) }
    //               if(e2 < Sentinel){
    //                 while(eS < e2){ indexS += 1; eS = esS(indexS) }
    //                 // eS >= e2 >= e1
    //                 if(e1 == eS){ // can synchronise
    //                   assert(e1 == e2)
    //                   // println("Three-way synchronisation on "+showEvent(e1))
    //                   val theNexts1 = nextsc1(index1)
    //                   val theNexts2 = nextsc2(index2)
    //                   val theNextsS = nextsS(indexS)
    //                   val newViews = Views.insert2States(
    //                     cptView, j1, theNexts1, j2, theNexts2)
    //                   for(newView <- newViews){
    //                     for(newSStates <- theNextsS){
    //                       addTrans(e1, newSStates, newView)
    //                       // println(sv+" -"+showEvent(e1)+"->\n  [ "+
    //                       //           showView(newSStates)+"] || ["+
    //                       //           showView(newView)+" ]")
    //                     }
    //                     Views.returnView(newView) // recycle
    //                   }
    //                   index1 += 1; e1 = esc1(index1)
    //                   index2 += 1; e2 = esc2(index2)
    //                   indexS += 1; eS = esS(indexS)
    //                 } // end of if(...) can synchronise
    //               }
    //             }
    //           } // end of outer while
    //         } // end of if(serverTrans != null)
    //       }
    //     }
    //   } // end of inner for
    // } // end of Case 5

    // if(checkDeadlock && deadlock){
    //   if(significant(sv)){
    //     println("Deadlock in "+sv); synchronized{ deadlocks += sv }
    //   }
    //   // else println("Insignificant deadlock in "+sv)
    // }

    // Views.returnView(cptView)
 



