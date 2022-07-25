package ViewAbstraction

import uk.ac.ox.cs.fdr.{Option => _, _} // hide fdr.Option
import scala.jdk.CollectionConverters._
import scala.collection.mutable.{Map,Stack,Set,ArrayBuffer,HashMap}
import RemapperP.Remapper

/** Class that builds transition systems, based on FDR.
  * @param fdrSession the FDR session object
  * @param superTypeNames the names of distinguished supertypes.  */
class FDRTransitionMap(fdrSession: FDRSession, fdrEvents: FDREvents){

  // ========= Build the transition systems.

  // IMPROVE: we create the transition function in one form, then transform it
  // to a different form.  Can this be improved?

  import FDRTransitionMap.{TransList,RenamingMap}

  /** A map representing a transition system.  Given a destination src, the map
    * returns the transitions from src. */ 
  type TransMap = Map[State, TransList]

  /** A map giving the types of the parameters of each state. */
  private val stateTypeMap0 = Map[ControlState, Array[Type]]()

  /** String representing st, using stateTypeMap0 for the types. */
  @inline private def show(st: State) = st.toStringX(stateTypeMap0(st.cs))

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
      if(id >= 0 && (args0.isEmpty || args0.head != (typeId, id))){
        println("adding identity"); (typeId, id)::args0
      }
      else args0
    val cs = machine.stateGroup(node).toInt 
    val ids = new Array[Identity](args1.length); var i = 0
    for((t,x) <- args1){ 
      try{ ids(i) = fdrEvents.getIdRemap(t)(x); i += 1 }
      catch{ case e: NoSuchElementException =>
        println(s"Not found ($t,$x)"); println(fdrEvents.getIdRemap(t))
        sys.exit()
      } // There is sometimes an exception here, but I don't understand why. 
    }
    stateTypeMap0.get(cs) match{
      case Some(ts) => { 
        assert(ts.length == args1.length, 
               "Error caused by having to add missing identity to process: "+
                 s"cs = $cs; id = $id\n"+ ts.mkString("<", ",", ">")+"\n"+
                 args1.mkString("<", ",", ">"))
      }
      case None => 
        val types: Array[Type] = 
          args1.map{ case (t,x) => fdrEvents.fdrTypeToType(t) }.toArray
        stateTypeMap0 += cs -> types
    }
    MyStateMap(family, cs, ids)
  }

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
// FIXME: I think we want BFS for the remapping strategy
      stack.push((root, rootState)); seen += rootState

      while(stack.nonEmpty){
        val (node, st) = stack.pop()
        // Map to normal form
        val types = stateTypeMap0(st.cs)
        def show1(st1: State) = { 
          require(st1.cs == st.cs); st1.toStringX(types)
        }
        val (normSt, map) = Remapper.normaliseState(st, types)
        println(show1(st)+" normalised to "+show1(normSt)+
          " via "+Remapper.show(map))

        // TODO: if st1 in dom transMap, remap from there.

        // Build up transitions from node in trans
        var trans = ArrayBuffer[(Int, State)]()
        var lastE = -1
        for(t <- machine.transitions(node).iterator.asScala) {
          val e = t.event.toInt 
          assert(lastE <= e); lastE = e // check events non-decreasing
          val dst = t.destination
          val dstState = nodeToState(machine, dst, family, id, typeId)
          trans += ((e, dstState))
          if(normSt != st || verbose)
            println(show1(st)+" -"+showEvent(e)+"-> "+show(dstState))
          if(!seen.contains(dstState)){
            stack.push((dst, dstState)); seen += dstState
          }
        } // end of for loop
        val transList = trans.toList; transMap += st -> transList

        // TODO: map transList under inverse of map, and store against st
        if(normSt != st){
          val inverse = Remapper.inverse(map)
          val (froms, tos) = Remapper.getFromsTos(inverse)
          println("Inverse mapping: "+Remapper.show(inverse))
          println("froms = "+froms.mkString(",")+
            "; tos = "+tos.mkString(","))
          assert(Remapper.applyMap(normSt, inverse, types) == st)
          val remappedTrans = trans.map{ case (e,dst) =>
            (fdrEvents.remapEvent(e, tos, froms),
              Remapper.applyMap(dst, inverse, stateTypeMap0(dst.cs)))
          }
          for((e1,dst1) <- remappedTrans)
            println(show1(normSt)+s" -${showEvent(e1)}-> "+show(dst1))

          // TODO: sort by event, and store
        }
      }
    }
    else println(s"$rootState already seen")
    rootState
  }

//   /** New version of augmentTransMap that tries to produce transitions by
//     * renaming those previously found for symmetrically bisimilar states. */
//   def newAugmentTransMap(
//     transMap: TransMap, seen: Set[State], machine: Machine,
//     family: Int, id: Int, typeId: Long, verbose: Boolean = false)
//       : State = {
//     val root = machine.rootNode
//     val rootState = nodeToState(machine, root, family, id, typeId)
//     // We'll perform a depth-first search.  stack will store Nodes, and the
//     // corresponding State values, that have to be expanded.
//     val stack = new Stack[(Node, State)]
//     stack.push((root, rootState)); seen += rootState
// // Does seen contain states done or just those that we've sen?

//     while(stack.nonEmpty){
//       val (node, st) = stack.pop()
//       val (st1,map) = RemapperP.Remapper.normaliseState(st)
//       // Get transitions of st1, either recalling them or producing them
//       val trans1 = transMap.get(st1) match{
//         case None => 
//           // Create transitions for st1, store and return
//           ???
//         case Some(trans2) => trans2
//       }
//       // produce transitions for st by remapping st1 by the inverse of map

//     }
//     rootState
//   }

  /* Code to build a renaming map from a list of pairs of events
   * (<(Event,Event)>), or a list of lists of pairs of events
   * (<<(Event,Event)>>) inside FDR.  We flatten into a single list of events,
   * e.g. < e1_, e2_ | (e1_,e2_) <- pairsList >.  This allows us to get away
   * with a single call into the FDR API, and seems the most efficient way. */

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
        println(".  Done"); renamingMapFromEventList(eventsList)

      case None => null
    }

  def mkRenamingMap(oRenamingFunc: Option[String], arg: String): RenamingMap =
    oRenamingFunc match{
      case Some(func) => 
        print("Making renaming map...")
        val eventsList: Array[String] =
          fdrSession.applyFunctionOrMap(fdrSession.evalSeqSeqOrSeq(_, unpair), 
                                        func, arg)
        println(".  Done"); renamingMapFromEventList(eventsList)

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
      val map = new HashMap[EventInt,List[EventInt]]
      for(i <- (0 until eventsList.length/2)){
        val e1 = fdrEvents.eventToInt(eventsList(2*i))
        val e2 = fdrEvents.eventToInt(eventsList(2*i+1))
        map.get(e1) match{
          case Some(es) => map += e1 -> (e2::es)
          case None => map += e1 -> List(e2)
        }
      }
      map
    }
  }

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
        transList = FDRTransitionMap.renameTransList(transList, renamingMap)

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

  /** The maximum control state so far. */
  def getMaxCS = stateTypeMap0.keysIterator.max

  /** Create stateTypeMap, giving the types of parameters of each state.  This
    * should be called after the transition maps of the components and servers
    * have been created. */
  def createStateTypeMap = {
    val maxCS = getMaxCS // stateTypeMap0.keysIterator.max
    // following two variables in package
    val minCS = stateTypeMap0.keysIterator.min
    println("minCS = "+minCS+"; maxCS = "+maxCS)
    val stateTypeMapArray = new Array[Array[Type]](maxCS-minCS+1)
    for((cs,ts) <- stateTypeMap0.iterator) stateTypeMapArray(cs-minCS) = ts
    State.setStateTypeMap(stateTypeMapArray, minCS)
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
    val pids = args0.map{ case (t,x) => 
      (fdrEvents.fdrTypeToType(t), fdrEvents.getIdRemap(t)(x)) }
    (cs, pids)
  }


}

// ==========================================================================

object FDRTransitionMap{
  /** List of transitions from a given state st: pairs (e, st') such that 
    * st -e-> st'.  This
    * list is sorted by events.*/
  type TransList = List[(EventInt, State)]

  type RenamingMap = Map[EventInt,List[EventInt]]

  /** Rename transitions according to renamingMap. */
  def renameTransList(transList: TransList, renamingMap: RenamingMap)
      : TransList = 
    transList.flatMap{ case(e,s1) =>
      renamingMap.get(e) match{
        case Some(es) => es.map(e2 => (e2,s1))
        case None => List((e,s1))
      }
    }.sortBy(_._1)
}



  // /** String defining take and drop functions. */
  // private val takeDropString =
  //   "let take(xs_, n_) = "+
  //     "if n_ == 0 or null(xs_) then <> else <head(xs_)>^take(tail(xs_), n_-1) "+
  //     "within let drop(xs_, n_) = "+
  //     "if n_ == 0 or null(xs_) then xs_ else drop(tail(xs_), n_-1) within "

  // private val Chunk = 500
