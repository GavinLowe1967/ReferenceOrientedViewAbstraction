package ViewAbstraction

import uk.ac.ox.cs.fdr.{Option => _, _} // hide fdr.Option
import scala.jdk.CollectionConverters._
import scala.collection.mutable.{Map,Stack,Set,ArrayBuffer}

/** Class that builds transition systems, based on FDR.
  * @param fdrSession the FDR session object
  * @param superTypeNames the names of distinguished supertypes.  */
class FDRTransitionMap(
  fdrSession: FDRSession, superTypeNames: Array[String])
{

  // ========= Information about types

  /* The various maps related to types (idRemaps, theNameMap, theTypeMap) are
   * initialised via calls to fdrTypeToType for each type, from Components.
   * This is before the transition systems themselves are created. */

  // assert(familyTypeNames.distinct.length == numTypes &&  
  //          superTypeNames.length == familyTypeNames.length)
  
  /** A map for a particular supertype, mapping, for each element x of that
    * supertype, the representation of x inside FDR to the representation used
    * here; elements of the subtype map onto an initial segment of the
    * naturals, and other (distinguished) values map onto negative ints. */
  private type IdRemap = Map[Int, Int]

  /** A map giving an IdRemap for each type, indexed by the representation of
    * the types inside FDR. */
  private val idRemaps = Map[Long, IdRemap]() 

  /** A map for a particular type, mapping from the representation used here to
    * the name from the script. */
  private type NameMap = Map[Identity, String]

  /** A map giving a NameMap for each type. */
  private val theNameMap = Map[Type, NameMap]()

  /** Get the NameMap.  Called after the transition system is built. */
  def getNameMap = theNameMap

  /** Map from the Longs used to represent types in FDR to the Ints used here.  
    * The latter are in the range [0..numTypes). 
    * 
    * The entry for type t is built by typeMap, the first time a parameter of
    * this type is encountered. */
  private val theTypeMap = Map[Long, Int]()

  /** Given the Long used to represent a type within FDR, return the
    * corresponding Int used here.  Also, if this is the first time we've seen
    * this type, calculate and store information about the type, updating
    * theTypeMap, fdrTypeIds, idRemaps and typeSizes.  */
  private def typeMap(t: Long): Type = theTypeMap.get(t) match{
    case Some(i) => i
    case None =>
      // This is the first time we've encountered this type
      val superTypeName = fdrSession.typeName(t)
      val i = superTypeNames.indexOf(superTypeName); assert(i >= 0)
      println(superTypeName+"\t"+t+"\t"+i)
      theTypeMap += t -> i 
      val (idRemap, nameMap, typeSize) =
        buildIdRemap(familyTypeNames(i), superTypeName)
      idRemaps += t -> idRemap; theNameMap += i -> nameMap;
      typeSizes(i) = typeSize; superTypeSizes(i) = idRemap.size
      distinguishedSizes(i) = superTypeSizes(i) - typeSize
      println("Supertype size = "+idRemap.size)
      println("Distinguished values = "+distinguishedSizes(i))
      i
  }

  def fdrTypeToType(t: Long): Type = typeMap(t)

  /** Build information about type typeName, with supertype superType. 
    * @return a triple: (1) an IdRemap, mapping the representation of each 
    * value inside FDR to the value used here; (2) a map from the values used
    * here to the names in the script; (3) the number of elements of the type
    * (excluding distinguished values of the supertype).*/
  private def buildIdRemap(typeName: String, superType: String)
      : (IdRemap, NameMap, Int) = {
    val idRemap = Map[Int, Int]() // the result
    val nameMap = Map[Int, String]() // map from values used here to script names
    // Values in the type and supertype
    val superTypeVals = fdrSession.getTypeValues(superType)
    val typeValues = fdrSession.getTypeValues(typeName)
    // Next ints to use for ids and distinguished values
    var nextId = 0; var nextDistinguished = -1

    // Build the mapping for each value of superType in turn.
    for(st <- superTypeVals){
      val id = fdrSession.symmetryValue(st) // Int representing st inside FDR
      if(typeValues.contains(st)){ idRemap += id -> nextId; nextId += 1 }
      else{ idRemap += id -> nextDistinguished; nextDistinguished -= 1 }
      nameMap += idRemap(id) -> st
      println(s"$id: $st -> ${idRemap(id)}")
    }

    (idRemap, nameMap, nextId)
  }

  // ========= Build the transition systems.

  // IMPROVE: we create the transition function in one form, then transform it
  // to a different form.  Can this be improved?

  /** A map representing a transition system.  Given a destination src, the map
    * returns a list of events e and states dst such that src -e-> dst.  This
    * list is sorted by events. */ 
  type TransMap = Map[State, List[(Int, State)]]

  /** A map giving the types of the parameters of each state. */
  private val stateTypeMap0 = Map[ControlState, Array[Type]]()

  /** Convert a Node into a State, using the node's state group as the
    * ControlState, and the node's variable values as the Identities,
    * prepended with id if non-negative and the identity is not already there,
    * and remapped using idRemap.
    * @param family the family of components from which this is taken, or -1 
    * for a server.
    * @param id the representation inside FDR of this process's identity, 
    * or -1 if this isn't a replicated component.
    * @param typeId the type identifier for the type of id. */
  private def nodeToState
    (machine: Machine, node: Node, family: Int, id: Int, typeId: Long)
      : State = {
    val variableVals = machine.variableValues(node).asScala.toList
    // Types and values for each variable map.
    val args0: List[(Long, Int)] =
      variableVals.map(vv => (vv.getType.longValue, vv.getValue.intValue))
    // Add in id if relevant
    // FIXME: this goes wrong if args0.head happens to equal id, by "chance".
    val args1 =
      if(id >= 0){
        if(args0.isEmpty || args0.head != (typeId, id)){
          println("adding identity"); (typeId, id)::args0 
        }
        else args0
      }
      else args0
    val cs = machine.stateGroup(node).toInt 
    val ids = State.getIdentityArray(args1.length); var i = 0
    for((t,x) <- args1){ ids(i) = idRemaps(t)(x); i += 1 }
    stateTypeMap0.get(cs) match{
      case Some(ts) => { 
        assert(ts.length == args1.length, 
               "Error caused by having to add missing identity to process: "+
                 s"cs = $cs; id = $id\n"+ ts.mkString("<", ",", ">")+"\n"+
                 args1.mkString("<", ",", ">"))
      }
      case None => 
        val types: Array[Type] = args1.map{ case (t,x) => typeMap(t) }.toArray
        // println(s"$cs -> ${types.mkString("<", ",", ">")}")
        stateTypeMap0 += cs -> types
    }
    MyStateMap(family, cs, ids) // potentially recycles ids
  }

  // Flag to cause transitions to be printed
  private val verbose = false

  /* Note: to make the following thread-safe, it is necessary to (1) protect
   * stateTypeMap0 in nodeToState; (2) protect transMap and seen within
   * augmentTransMap.  It might be sensible to change the accesses to seen to
   * combine the contains and +=. */

  /** Explore machine, adding all transitions to transMap.  seen contains those
    * states already explored.  Also log all events with fdrSession. 
    * @param family the family of components from which this is taken, or -1 
    * for a server.
    * @param id the identity of the process represented by this machine if it
    * is a component, or -1 otherwise.
    * @param typeId the FDR type identifier for the type of id 
    * (if non-negative). 
    * @return the root state as a State. */
  def augmentTransMap(
    transMap: TransMap, seen: Set[State], machine: Machine,
    family: Int, id: Int, typeId: Long, verbose: Boolean = false)
      : State = {
    val root = machine.rootNode
    val rootState = nodeToState(machine, root, family, id, typeId)
    if(!seen.contains(rootState)){
      // We'll perform a depth-first search.  stack will store Nodes, and the
      // corresponding State values, that have to be expanded.
      val stack = new Stack[(Node, State)]
      stack.push((root, rootState)); seen += rootState

      while(stack.nonEmpty){
        val (node, st) = stack.pop
        // Build up transitions from node in trans
        var trans = ArrayBuffer[(Int, State)]()
        var lastE = -1
        for(t <- machine.transitions(node).iterator.asScala) {
          val e = t.event.toInt 
          assert(lastE <= e); lastE = e // check events non-decreasing
          val dst = t.destination
          val dstState = nodeToState(machine, dst, family, id, typeId)
          trans += ((e, dstState))
          if(verbose)
            println(st.toString00+" -"+fdrSession.eventToString(e)+"-> "+
                      dstState.toString00)
          // assert(dstState._1 >= 0)
          if(!seen.contains(dstState)){
            stack.push((dst, dstState)); seen += dstState
          }
        } // end of for loop
        transMap += st -> trans.toList
      }
    }
    else println(s"$rootState already seen")
    rootState
  }

  /** New version of augmentTransMap that tries to produce transitions by
    * renaming those previously found for symmetrically bisimilar states. */
  def newAugmentTransMap(
    transMap: TransMap, seen: Set[State], machine: Machine,
    family: Int, id: Int, typeId: Long, verbose: Boolean = false)
      : State = {
    val root = machine.rootNode
    val rootState = nodeToState(machine, root, family, id, typeId)
    // We'll perform a depth-first search.  stack will store Nodes, and the
    // corresponding State values, that have to be expanded.
    val stack = new Stack[(Node, State)]
    stack.push((root, rootState)); seen += rootState
// Does seen contain states done or just those that we've sen?

    while(stack.nonEmpty){
      val (node, st) = stack.pop
      val (st1,map) = RemapperP.Remapper.normaliseState(st)
      // Get transitions of st1, either recalling them or producing them
      val trans1 = transMap.get(st1) match{
        case None => 
          // Create transitions for st1, store and return
          ???
        case Some(trans2) => trans2
      }
      // produce transitions for st by remapping st1 by the inverse of map

    }
    rootState
  }

  /** String defining take and drop functions. */
  private val takeDropString =
    "let take(xs_, n_) = "+
      "if n_ == 0 or null(xs_) then <> else <head(xs_)>^take(tail(xs_), n_-1) "+
      "within let drop(xs_, n_) = "+
      "if n_ == 0 or null(xs_) then xs_ else drop(tail(xs_), n_-1) within "

  private val Chunk = 500

  /* Code to build a renaming map from a list of pairs of events
   * (<(Event,Event)>), or a list of lists of pairs of events
   * (<<(Event,Event)>>) inside FDR.  We flatten into a single list of events,
   * e.g. < e1_, e2_ | (e1_,e2_) <- pairsList >.  This allows us to get away
   * with a single call into the FDR API, and seems the most efficient way. */

  type RenamingMap = Map[EventInt,List[EventInt]]

  private def unpair(name: String) = s"< e1_, e2_ | (e1_,e2_) <- ($name) >"

  /** Optionally make a map representing the renaming of a state machine, from a
    * string that evaluates to the corresponding list of pairs or list of
    * lists of pairs. */
  def mkRenamingMap(oRenamingName: Option[String]): RenamingMap = 
    oRenamingName match{
      case Some(renameName) =>
        print("Making renaming map...")
        val eventsList: Array[String] =
          fdrSession.evalSeqSeqOrSeq(renameName, unpair)
        val map = renamingMapFromEventList(eventsList)
        println(".  Done")
        map

      case None => null
    }

  def mkRenamingMap(oRenamingFunc: Option[String], arg: String): RenamingMap =
    oRenamingFunc match{
      case Some(func) => 
        print("Making renaming map...")
        val eventsList: Array[String] =
          fdrSession.applyFunctionOrMap(fdrSession.evalSeqSeqOrSeq(_, unpair), 
                                        func, arg)
          // fdrSession.evalSeqSeqOrSeq(s"$func($arg)", unpair)
        val map = renamingMapFromEventList(eventsList)
        println(".  Done")
        map

      case None => null
    }

  /** Create the map
    * { eventsList(2*i) -> eventsList(2*i+1) | i <- [0..eventsList.length/2 }.
    */
  private def renamingMapFromEventList(eventsList: Array[String])
      : RenamingMap = {
    assert(eventsList.length%2 == 0)
    if(eventsList.isEmpty){ println("Empty renaming map"); null }
    else{
      // IMPROVE: consider using thread-safe map here
      // IMPROVE: use parallel here
      val map = new scala.collection.mutable.HashMap[EventInt,List[EventInt]]
      for(i <- (0 until eventsList.length/2)){
        // I believe the following should work, because the alphabets have
        // been created prior to this, so all the events should have been
        // initialised.
        val e1 = fdrSession.eventToInt(eventsList(2*i))
        val e2 = fdrSession.eventToInt(eventsList(2*i+1))
        map.synchronized{
          map.get(e1) match{
            case Some(es) => map += e1 -> (e2::es)
            case None => map += e1 -> List(e2)
          }
        }
      }
      map
    }
  }

  /** Rename transitions according to renamingMap. */
  def renameTransList(transList: List[(EventInt, State)], 
                      renamingMap: RenamingMap)
      : List[(EventInt, State)] = 
    transList.flatMap{ case(e,s1) =>
      renamingMap.get(e) match{
        case Some(es) => es.map(e2 => (e2,s1))
        case None => List((e,s1))
      }
    }.sortBy(_._1)

  /** Build a transition map corresponding to name.
    * @param alpha the alphabet of this process in the system; transitions 
    * outside this alphabet should be dropped.
    * @param family the family of components from which this is taken, or -1 
    * for a server.
    * @param oRenamingString optionally a String which, when evaluated by FDR,
    * gives the renaming relation (as a list of pairs) to be applied to the
    * state machine.
    * @return a triple consisting of (1) the initial state, as a State, (2) the 
    * transition map as a map from States to a pair of parallel arrays, giving
    * each event and list of post-states. */
  def buildTransMap(name: String, alpha: Set[EventInt], family: Int, 
                    oRenamingString: Option[String])
      : (State, Map[State, (Array[EventInt], Array[List[State]])]) = {
    val machine: Machine = fdrSession.evalProc(name)
    val transMap = Map[State, List[(Int, State)]]()
    val seen = Set[State]()
    val init = augmentTransMap(transMap, seen, machine, family, -1, -1)
    // Map representing renaming to be applied to state machine
    // val renaming = mkRenamingPairs(oRenamingString)
    val renamingMap: Map[EventInt,List[EventInt]] = 
      mkRenamingMap(oRenamingString)
    
    // Now convert into more convenient form, giving a map from states to a
    // pair of parallel arrays, giving each event and list of post-states.
    println("Finalising transition system")
    val newTransMap = Map[State, (Array[EventInt], Array[List[State]])]()
    for(s <- seen){
      var transList: List[(EventInt, State)] = transMap(s)
      if(renamingMap != null)
        // Rename every event according to renamingMap, and re-sort
        transList = renameTransList(transList, renamingMap)

      val es = new ArrayBuffer[EventInt]
      val nexts = new ArrayBuffer[List[State]]
      while(transList.nonEmpty){
        val e = transList.head._1
        val (matches, rest) = transList.span(_._1 == e)
        transList = rest
        if(matches.nonEmpty){
          if(alpha.contains(e) || e == Tau){ 
            es += e; nexts += matches.map(_._2) 
          }
        }
      }
      es += Int.MaxValue // sentinel
      newTransMap(s) = (es.toArray, nexts.toArray)
    }
 
    (init, newTransMap)
  }

  /** Create stateTypeMap, giving the types of parameters of each state.  This
    * should be called after the transition maps of the components and servers
    * have been created. */
  def createStateTypeMap = {
    val maxCS = stateTypeMap0.keysIterator.max
    // following two variables in package
    val minCS = stateTypeMap0.keysIterator.min
    println("minCS = "+minCS+"; maxCS = "+maxCS)
    val stateTypeMapArray = new Array[Array[Type]](maxCS-minCS+1)
    for((cs,ts) <- stateTypeMap0.iterator) stateTypeMapArray(cs-minCS) = ts
    State.setStateTypeMap(stateTypeMapArray, minCS)
    MyStateMap.doneCompiling
  }

  /** Given a string representing a process, get its control state and the
    * values representing its parameters. */
  def getProcInfo(st: String): (ControlState, List[ProcessIdentity]) = {
    val machine: Machine = fdrSession.evalProc(st)
    val node = machine.rootNode
    val cs = machine.stateGroup(node).toInt
    val variableVals = machine.variableValues(node).asScala.toList
    val args0: List[(Long, Int)] =
      variableVals.map(vv => (vv.getType.longValue, vv.getValue.intValue))
    val pids = args0.map{ case (t,x) => (fdrTypeToType(t), idRemaps(t)(x)) }
    (cs, pids)
  }


}
