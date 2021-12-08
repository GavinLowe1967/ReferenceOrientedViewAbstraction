package ViewAbstraction

import RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}

// FIXME: there's a lot of repeated code between here and EffectOnUnification

class SingleRefEffectOnUnification(
  pre: Concretization, post: Concretization, cv: ComponentView){

  /* A few object variables, extracted directly from pre, post and cv, used in
   * several functions. */
  private val servers = pre.servers
  require(servers == cv.servers && servers.isNormalised)
  private val postServers = post.servers
  private val changedServers = servers != postServers
  private val preCpts = pre.components; private val postCpts = post.components
  require(preCpts.length == postCpts.length)
  private val cpts = cv.components
  if(debugging) StateArray.checkDistinct(cpts)
  // ID of principal of cv
  private val (cvpf, cvpid) = cv.principal.componentProcessIdentity
  // IDs of components in pre, cv
  private val preCptIds = preCpts.map(_.componentProcessIdentity)
  private val cptIds = cpts.map(_.componentProcessIdentity)

  import Unification.UnificationList // = List[(Int,Int)]
  // Contains (i,j) if cpts(i) is unified with preCpts(j)

  // A representation of map |> post.servers
  import ComponentView.ReducedMap 

  type CombineResult1 = 
    ArrayBuffer[(RemappingMap, Array[State], UnificationList, ReducedMap)]

  /** The part of the result corresponding to secondary induced transitions.
    * The Int field is the index of the component in pre/post that gains
    * access to cv.principal. */
  type CombineResult2 = ArrayBuffer[(Array[State], UnificationList, Int)]

  /** Variables in which we build up the result. */
  private val result = new CombineResult1
  private val result2 = new CombineResult2

  /** Bit map indicating which components have changed state. */
  private val changedStateBitMap = getChangedStateBitMap()

  /** Bitmap showing which components changed state between preCpts and
    * postCpts. */
  @inline private 
  def getChangedStateBitMap(): Array[Boolean] = {
    val changedStateBitMap = new Array[Boolean](preCpts.length); var i = 0
    while(i < preCpts.length){
      changedStateBitMap(i) = preCpts(i) != postCpts(i); i += 1
    }
    changedStateBitMap
  }

  /** A NextArgMap, containing values greater than anything in pre or post. */
  private val nextArg: NextArgMap = pre.getNextArgMap
  post.updateNextArgMap(nextArg)

  /** The main function. */
  def apply(): (CombineResult1, CombineResult2) = {
    val map0 = servers.remappingMap(cv.getParamsBound)
    // All params in post.servers but not in pre.servers, as a bitmap.
    val newServerIds: Array[Array[Boolean]] = getNewServerIds
    val allUnifs = Unification.allUnifs(map0, preCpts, cpts)

    for((map1, unifs) <- allUnifs){
      //println(Remapper.show(map1)+"; "+unifs)
      if(isSufficientUnif(unifs)){
        // Parameters to map params of cv to, in order to create result-defining
        // map.
        val otherArgs = mkOtherArgsMap(newServerIds, map1, unifs)
        // Primary result-defining maps
        val rdMaps = extendMap(map1,otherArgs)
        // Extend with extra linkages and fresh parameters
        for(rdMap <- rdMaps) extendMapping(unifs, rdMap)
      }
      else println("Not sufficient unif "+unifs)
    }
    (result,result2)
  }

  /** All params in post.servers but not in pre.servers, as a bitmap. */
  private def getNewServerIds: Array[Array[Boolean]] =
    ServerStates.newParamsBitMap(servers, post.servers)

  @inline private def isSufficientUnif(unifs: UnificationList)
      : Boolean = {
    // Is there a unification with a component that changes state?
    @inline def changingUnif = {
      var us = unifs; var sufficientUnif = false
      while(!sufficientUnif && us.nonEmpty){
        sufficientUnif = changedStateBitMap(us.head._2); us = us.tail
      }
      sufficientUnif
    }

    if(unifs.length == cpts.length && unifs.contains((0,0))) false
    else true
// IMPROVE:  below
      // else if(changedServers) true 
      // else changingUnif
  }

  /** Create a bit map corresponding to an OtherArgMap and containing all
    * parameters: (1) in newServerIds (parameters in post.servers but not
    * pre.servers), or (2) in a unified component of post.cpts; (3) in
    * post.cpts for a component to which cv.principal gains a reference.  But
    * excluding parameters of servers or those in the range of map1 in all
    * cases.  */
  @inline private 
  def mkOtherArgsMap(
    newServerIds: BitMap, map1: RemappingMap, unifs: UnificationList)
      : OtherArgMap = {
    // (1) parameters in newServerIds
    val otherArgsBitMap = newServerIds.map(_.clone); var us = unifs
    while(us.nonEmpty){
      val (j, i) = us.head; us = us.tail
      // (2) Add parameters of postCpts(i), which is unified with a component
      // of cv.
      postCpts(i).addIdsToBitMap(otherArgsBitMap, servers.idsBitMap) 
      // (3) If this is the unification of the principal of cv, which changes
      // state and gains a reference to another component c, include the
      // parameters of c from postCpts.
      if(j == 0 && changedStateBitMap(i)) addIdsFromNewRef(otherArgsBitMap, i)
    }
    Remapper.removeFromBitMap(map1, otherArgsBitMap)
    Remapper.makeOtherArgMap(otherArgsBitMap)
  }

  /** Add to otherArgsBitMap any parameters of a component c to which preCpts(i)
    * gains a reference as the result of the transition. */ 
  @inline private 
  def addIdsFromNewRef(otherArgsBitMap: Array[Array[Boolean]], i: Int) = {
    val prePids = preCpts(i).processIdentities
    val postPids = postCpts(i).processIdentities
    val serverIds = servers.idsBitMap
    // Find which parameters are gained
    for(k <- 1 until postPids.length){
      val pid = postPids(k)
      if(!isDistinguished(pid._2) && !prePids.contains(pid)){
        val c = StateArray.find(pid, postCpts)
        // Assumptions imply pid must be in postCpts, except under singleRef.
        if(c != null) c.addIdsToBitMap(otherArgsBitMap, serverIds)
        else assert(singleRef)
      }
    }
  }

  /** Extend map, mapping undefined parameters to parameters in otherArgs, or
    * not. */
  private def extendMap(map: RemappingMap, otherArgs: OtherArgMap)
      : ArrayBuffer[RemappingMap] = {
    val result = new ArrayBuffer[RemappingMap]

    /** Extend map, remapping parameters from (t,i) onwards. */
    def rec(t: Int, i: Int): Unit = {
      // println(s"$t, $i), ${otherArgs.mkString("; ")}")
      if(t == numTypes) result += Remapper.cloneMap(map)  // done this branch
      else if(i == map(t).length) rec(t+1, 0) // advance
      else if(map(t)(i) >= 0) rec(t, i+1) // advance
      else{
        val isId = cptIds.contains((t,i)) // Is this an identity?
        // map (t,i) to each element of otherArgs(t)
        var toDoIds = otherArgs(t); var doneIds = List[Identity]()
        // Inv: reverse(doneIds) ++ toDoIds = otherArgs(t)
        while(toDoIds.nonEmpty){
          val id1 = toDoIds.head; toDoIds = toDoIds.tail
          // Don't map an identity to an identity
          if(!(isId && preCptIds.contains((t,id1)))){
            otherArgs(t) = append1(doneIds, toDoIds) // temporary update (*)
            map(t)(i) = id1  // temporary update (+)
            // println(s"($t,$i) -> $id1")
            rec(t, i+1)
            map(t)(i) = -1   // backtrack (+)
          }
          doneIds ::= id1 // order doesn't matter
        } // end of while loop
        otherArgs(t) = doneIds // undo (*)
        // Also include case of not updating this param
        rec(t, i+1)
      }
    } // end of rec

    rec(0,0); result
  }


  // private def extendUnif(unifs: UnificationList, mapU: RemappingMap) = {  }

  /** Representation of a linkage.  A tuple (i, j, id) represents a linkage
    * between cpts(i) and preCpts(j) on parameter id. */
  private type Linkage = (Int,Int,Identity)

  /** Find all the linkages implied by rdMap.  All tuples (i, j, id1) such that
    * id is a parameter of cpts(i), id1 = rdMap(id) is a parameter of
    * preCpts(j), and this doesn't represent a unification of components (with
    * identities id/id1). */
  private def findLinkages(
    unifs: UnificationList, rdMap: RemappingMap)
      : ArrayBuffer[Linkage] = {
    // indices of unified cpts in cv, resp, pre
    val cvUnifs = unifs.map(_._1); val preUnifs = unifs.map(_._2)
    val result = new ArrayBuffer[(Int, Int, Identity)]
    for(t <- 0 until numTypes; id <- 0 until rdMap(t).length){
      val id1 = rdMap(t)(id)
      if(id1 >= 0){
        // j such that id1 is the identity of preCpts(j), resp, all j such
        // that id1 is a reference of preCpts(j); and in each case preCpts(j)
        // is not a unified component.
        var idJ = -1; var refJs = List[Int]()
        for(j <- 0 until preCpts.length; if !preUnifs.contains(j))
          if(preCpts(j).hasPID(t,id1)){ assert(idJ < 0); idJ = j }
          else if(preCpts(j).processIdentities.contains((t,id1))) refJs ::= j
        if(idJ >= 0){  
          // Find all i such that id is a reference of cpts(i), not unified
          for(i <- 0 until cpts.length)
            if(!cvUnifs.contains(i) && cpts(i).hasRef(t,id))
              result += ((i, idJ, id1))
        }
        if(refJs.nonEmpty)
          // Find i with identity id and not unified, if any
          for(i <- 0 until cpts.length)
            if(cpts(i).hasPID(t,id) && !cvUnifs.contains(i))
              for(j <- refJs) result += ((i, j, id1))
      }
    }

    // Linkages for condition (c).  Iterate through the parameters of
    // cv.principal.
    val cvPrincParams = cv.principal.processIdentities
    for(i <- 1 until cvPrincParams.length){
      val (t,id) = cvPrincParams(i)
      if(!isDistinguished(id)){
        val id1 = rdMap(t)(id)
        // Are id and id1 missing parameters for cv, pre, respectively?
        if(id1 >= 0 && preCpts(0).processIdentities.contains((t,id1)) &&
            !cptIds.contains((t,id)) && !preCptIds.contains((t,id1))){
          // println(s"Missing $id -> $id1")
          result += ((0, 0, id1))
        }
      }
    }

    result
    // IMPROVE: use bitmaps for parameters
  }

  /** Given a result-defining map rdMap that creates a linkage between c1 =
    * cpts(i) and c2 = preCpts(j), find all extensions that maps each
    * parameter of c1 to a parameter of c2, or not, and add each to result. */
  private def extendForLinkage(
    rdMap: RemappingMap, i: Int, j: Int, result: ArrayBuffer[RemappingMap])
  = {
    val c1 = cpts(i); val c2 = preCpts(j)
    val c1Params = c1.processIdentities; val c2Params = c2.processIdentities

    // Create otherArgMap contaiing all params of c2 not in range rdMap
    val otherArgs = Remapper.newOtherArgMap
    for(ix <- 0 until c2.length){
      val (t,id) = c2Params(ix)
      if(!rdMap(t).contains(id) && !otherArgs(t).contains(id))
        otherArgs(t) ::= id
    }
    // println(s"otherArgs = "+otherArgs.mkString("; "))

    // Extend rdMap over params of c1 from ix onwards, based on otherArgs
    def rec(ix: Int): Unit = {
      if(ix == c1.length) result += Remapper.cloneMap(rdMap)
      else{
        val (t,id1) = c1Params(ix)
        if(!isDistinguished(id1) && rdMap(t)(id1) < 0){
          val isId = cptIds.contains((t,i)) // Is this an identity?
          // map (t,i) to each element of otherArgs(t)
          var toDoIds = otherArgs(t); var doneIds = List[Identity]()
          // Inv: reverse(doneIds) ++ toDoIds = otherArgs(t)
          while(toDoIds.nonEmpty){
            val id1 = toDoIds.head; toDoIds = toDoIds.tail
            // Don't map an identity to an identity
            if(!(isId && preCptIds.contains((t,id1)))){
              otherArgs(t) = append1(doneIds, toDoIds) // temporary update (*)
              rdMap(t)(i) = id1  // temporary update (+)
              // println(s"($t,$i) -> $id1")
              rec(ix+1)
              rdMap(t)(i) = -1   // backtrack (+)
            }
            doneIds ::= id1 // order doesn't matter
          } // end of while loop
          otherArgs(t) = doneIds // undo (*)
        } // end of if(!isDistinguished ... )
        // Also don't map (t,i) to anything
        rec(ix+1)
      }
    } // end of rec

// IMPROVE: if otherArgs is empty, just add rdMap
    rec(0); result
  }

  /** Extend rdMap corresponding to all linkages in linkages.  Note: this might
    * create new linkages. */
  private def extendForLinkages(
    rdMap: RemappingMap, linkages: ArrayBuffer[Linkage])
      : ArrayBuffer[RemappingMap] = {
    assert(linkages.length <= 1) // FIXME
    // We iterate through linkages.  current represents the maps produced on
    // the previous round.
    var current = new ArrayBuffer[RemappingMap]; current += rdMap
    for(ix <- 0 until linkages.length){
      val (i, j, _) = linkages(ix)
      val res = new ArrayBuffer[RemappingMap]
      for(map <- current) extendForLinkage(map, i, j, res)
      current = res
    }

    current
  }

  /** Extend the result-defining map rdMap, based on unifications unifs, to
    * produce all representative extensions, recursively mapping parameters
    * based on linkages, and then mapping other parameters to fresh
    * parameters.  For each such map, add an appropriate tuple to result. */
  private def extendMapping(unifs: UnificationList, rdMap: RemappingMap) = {
    val linkages = findLinkages(unifs, rdMap)
    val extendedMaps = extendForLinkages(rdMap, linkages)
    for(map1 <- extendedMaps){
      val newLinkages = findLinkages(unifs, map1)
      if(newLinkages.forall{ case (i,j,_) => linkages.exists{ case (ii,jj,_) =>
          ii == i && jj == j }}){
        // map remaining params to fresh and add to result
        mapUndefinedToFresh(map1)
        val newCpts = Remapper.applyRemapping(map1, cpts)
        val reducedMapInfo: ReducedMap =
          if(unifs.isEmpty) Remapper.rangeRestrictTo(map1, postServers)
          else null
        result += ((map1, newCpts, unifs, reducedMapInfo))
      }
      else{
        println(s"pre = $pre;\n cv = $cv;\n unifs = $unifs; rdMap = "+
          Remapper.show(rdMap)+s"; linkages = $linkages; map1 = "+
          Remapper.show(map1))
        sys.exit
// FIXME: recurse based on linkages in newLinkages not represented in linkages.
      }
    }
    // resultX
  }

  /** Extend map to map all undefined values to distinct fresh values. */
  private def mapUndefinedToFresh(map: RemappingMap) = {
    for(t <- 0 until numTypes){
      var next = nextArg(t)
      for(i <- 0 until map(t).length)
        if(map(t)(i) < 0){ map(t)(i) = next; next += 1 }
    }
  }


  // ========= Hooks for testing

  private val outer = this

  /** Object providing hooks for testing. */
  object TestHooks{
    /** The OtherArgMap corresponding to map and unifs. */
    def mkOtherArgs(map: RemappingMap, unifs: UnificationList): OtherArgMap = 
      mkOtherArgsMap(getNewServerIds, map, unifs)

    val extendMap = outer.extendMap _

    val findLinkages = outer.findLinkages _

    val extendForLinkages = outer.extendForLinkages _

    val isSufficientUnif = outer.isSufficientUnif _

    /** Extend the result-defining map rdMap, based on unifications unifs, to
      * produce all representative extensions, recursively mapping parameters
      * based on linkages, and then mapping other parameters to fresh
      * parameters. Return all resulting maps. */
    def extendMapping(unifs: UnificationList, rdMap: RemappingMap)
        : ArrayBuffer[RemappingMap] = {
      result.clear
      outer.extendMapping(unifs, rdMap)
      val res = result.map(_._1); result.clear; res
    }

  }

}
