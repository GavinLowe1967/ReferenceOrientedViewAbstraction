package ViewAbstraction

import RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}

class RemappingExtender(pre: Concretization, post: Concretization, cv: ComponentView){
  /* A few object variables, extracted directly from pre and cv, used in
   * several functions. */
  private val preCpts = pre.components;
  private val cpts = cv.components

  // IDs of components in pre, cv
  private val preCptIds = preCpts.map(_.componentProcessIdentity)
  private val cptIds = cpts.map(_.componentProcessIdentity)

  /** A NextArgMap, containing values greater than anything in pre or post. */
  private val nextArg: NextArgMap = pre.getNextArgMap
  post.updateNextArgMap(nextArg)

  import Unification.UnificationList // = List[(Int,Int)]

  /** Representation of a linkage.  A tuple (i, j) represents a linkage
    * between cpts(i) and preCpts(j). */
  private type Linkage = (Int,Int)

  /** Find all the linkages for part (b) implied by rdMap.  All tuples (i, j,
    * id1) such that id is a parameter of cpts(i), id1 = rdMap(id) is a
    * parameter of preCpts(j), with one of those being the identity; and such
    * this doesn't represent a unification of components (with identities
    * id/id1). */
  def findLinkages(unifs: UnificationList, rdMap: RemappingMap)
      : ArrayBuffer[Linkage] = {
    // indices of unified cpts in cv, resp, pre
    val cvUnifs = unifs.map(_._1); val preUnifs = unifs.map(_._2)
    val result = new ArrayBuffer[Linkage]

    // Iterate through rdMap
    for(t <- 0 until numTypes; id <- 0 until rdMap(t).length){
      val id1 = rdMap(t)(id)
      if(id1 >= 0){
        // Set idJ to j such that id1 is the identity of preCpts(j), or -1 if
        // no such; set refJs to all j such that id1 is a reference of
        // preCpts(j); and in each case preCpts(j) is not a unified component.
        var idJ = -1; var refJs = List[Int]()
        for(j <- 0 until preCpts.length; if !preUnifs.contains(j))
          if(preCpts(j).hasPID(t,id1)){ assert(idJ < 0); idJ = j }
          else if(preCpts(j).processIdentities.contains((t,id1))) refJs ::= j
        if(idJ >= 0){  
          // Find all i such that id is a reference of cpts(i), not unified
          for(i <- 0 until cpts.length)
            if(!cvUnifs.contains(i) && cpts(i).hasRef(t,id))
              result += ((i, idJ))
        }
        if(refJs.nonEmpty)
          // Find i with identity id and not unified, if any
          for(i <- 0 until cpts.length)
            if(cpts(i).hasPID(t,id) && !cvUnifs.contains(i))
              for(j <- refJs) result += ((i, j))
      }
    }
    result
    // IMPROVE: use bitmaps for parameters
  }

// IMPROVE: below isn't what we want.
  /** Linkages for condition (c). */
  def findLinkagesC(unifs: UnificationList, rdMap: RemappingMap)
      : ArrayBuffer[Linkage] = {
    val result = new ArrayBuffer[Linkage]
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
          result += ((0, 0))
        }
      }
    }

    result
    // IMPROVE: use bitmaps for parameters
  }

  /** Extend map to map all undefined values to distinct fresh values. */
  @inline  def mapUndefinedToFresh(map: RemappingMap) = {
    for(t <- 0 until numTypes){
      var next = nextArg(t)
      for(i <- 0 until map(t).length)
        if(map(t)(i) < 0){ map(t)(i) = next; next += 1 }
    }
  }

  /** Given a result-defining map rdMap that creates a linkage between c1 =
    * cpts(i) and c2 = preCpts(j), find all extensions that maps each
    * parameter of c1 to a parameter of c2, or not; but avoiding mapping to
    * elements of resultRelevantParams.  Add each to result. */
  def extendForLinkage(
    rdMap: RemappingMap, resultRelevantParams: BitMap, 
    i: Int, j: Int, result: ArrayBuffer[RemappingMap])
  = {
    val c2 = preCpts(j); val c2Params = c2.processIdentities
    // Create otherArgMap containing all params of c2 not in range rdMap
    val otherArgs = Remapper.newOtherArgMap
    for(ix <- 0 until c2.length){
      val (t,id) = c2Params(ix)
      if(!resultRelevantParams(t)(i) && !rdMap(t).contains(id) && 
          !otherArgs(t).contains(id))
        otherArgs(t) ::= id
    }
    //println("extendForLinkage: "+otherArgs.mkString("; "))
    extendMapOverComponent(rdMap, cpts(i), otherArgs, result)
  }

  /** Find all consistent extensions of map over the parameters of c, mapping
    * each parameter to an element of otherArgs, or not.  Add all such to
    * result. */
  def extendMapOverComponent(
    map: RemappingMap, c: State, otherArgs: OtherArgMap, 
    result: ArrayBuffer[RemappingMap]) 
  = {
    val cParams = c.processIdentities

    /* Extend map over params of c1 from ix onwards, based on otherArgs. */
    def rec(ix: Int): Unit = {
      if(ix == c.length) result += Remapper.cloneMap(map)
      else{
        val (t,id0) = cParams(ix)
        if(!isDistinguished(id0) && map(t)(id0) < 0){
          val isId = cptIds.contains((t,id0)) // Is this an identity?
          // map (t,id0) to each element of otherArgs(t)
          var toDoIds = otherArgs(t); var doneIds = List[Identity]()
          // Inv: reverse(doneIds) ++ toDoIds = otherArgs(t)
          while(toDoIds.nonEmpty){
            val id1 = toDoIds.head; toDoIds = toDoIds.tail
            // Don't map an identity to an identity
            if(!(isId && preCptIds.contains((t,id1)))){
              otherArgs(t) = append1(doneIds, toDoIds) // temporary update (*)
              map(t)(id0) = id1  // temporary update (+)
              rec(ix+1)
              map(t)(id0) = -1   // backtrack (+)
            }
            doneIds ::= id1 // order doesn't matter
          } // end of while loop
          otherArgs(t) = doneIds // undo (*)
        } // end of if(!isDistinguished ... )
        // Also don't map (t,i) to anything
        rec(ix+1)
      }
    } // end of rec

// // IMPROVE: if otherArgs is empty, just add rdMap
    rec(0)
  }


  /** Implementation of makeExtensions from the paper.  Create all required
    * extensions of result-defiling map rdMap.  Add all such to extensions.
    * doneB gives the instances of condition (b) that we have dealt with so
    * far.  Note: rdMap may be mutated. */
  def makeExtensions(
    unifs: UnificationList, resultRelevantParams: BitMap, 
    rdMap: RemappingMap, doneB: List[(Int,Int)], 
    extensions: ArrayBuffer[RemappingMap])
      : Unit = {
    val linkagesC = findLinkagesC(unifs, rdMap)
    if(linkagesC.nonEmpty) ???
    else{
      val linkagesB = findLinkages(unifs, rdMap)
      // IMPROVE: pass doneB to linkagesB
      val newLinkages = 
        linkagesB.filter( pair => !doneB.contains(pair) ).distinct
      //println("makeExtensions: "+newLinkages)
      if(newLinkages.isEmpty){ // map remaining params to fresh
        mapUndefinedToFresh(rdMap); extensions += rdMap
      }
      else{
        val (i,j) = newLinkages.head
        // FIXME: need to respect doneB below
        val extendedMaps = new ArrayBuffer[RemappingMap]
        extendForLinkage(rdMap, resultRelevantParams, i, j, extendedMaps)
        for(eMap <- extendedMaps) 
          makeExtensions(unifs, resultRelevantParams, eMap, 
            (i,j)::doneB, extensions)
      }
    }
  }

}
