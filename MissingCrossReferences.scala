package ViewAbstraction

import scala.collection.mutable.ArrayBuffer
import RemapperP.Remapper

/** Information about an induced transition.  This corresponds to transition
  * trans = pre -e-> post inducing
  * cv == (pre.servers, oldCpts) -> (post.servers, newCpts) == newView.*/
class InducedTransitionInfo(
  newView: ReducedComponentView, val trans: Transition,
  oldCpts: Array[State], val cv: ComponentView, newCpts: Array[State]
){
  require(trans.pre.components.length <= 3 && cv.components.length <= 2)
  require(trans.pre.servers == cv.servers)

  @inline def servers = cv.servers

  @inline def preCpts = trans.pre.components

  @inline def cpts = oldCpts

  @inline def prePrincipal = preCpts(0)

  /** Has newView been found already? */
  private var newViewFound = false

  /** Record that newView has already been seen, so this is redundant. */
  def markNewViewFound = synchronized{ newViewFound = true }

  /** Has newView been marked as found? */
  def isNewViewFound = synchronized{ newViewFound }

  /** Does views contain newView?  Store the result. */
  def isNewViewFound(views: ViewSet) = synchronized{
    newViewFound ||
    (if(views.contains(newView)){ newViewFound = true; true } 
    else false)
  }

  /** Get the ComponentView corresponding to this, setting its creation
    * information. */
  def get: ComponentView = {
    val v =  ComponentView.fromReducedComponentView(newView)
    v.setCreationInfoIndirect(trans, oldCpts, cv, newCpts)
    v
  }

  /** An InducedTransitionInfo extending this, instantiating oldCpts with
    * cpts. */
  def extend(cpts: Array[State]) = {
    require(lazyNewEffectOnStore && 
      (oldCpts == null || oldCpts.sameElements(cpts)))
    new InducedTransitionInfo(newView, trans, cpts, cv, newCpts)
  }

  /** The common missing references associated with this. */
  def commonMissingRefs =
    SingleRefEffectOnUnification.commonMissingRefs(preCpts, oldCpts).toArray

  // import InducedTransitionInfo.{EmptyReducedComponentView,newCrossRefs}

  // /** The new missing cross reference views 
  //   * formed by extending map0 so as to produce cpts1. */
  // @inline private 
  // def newMissingCrossRefs(
  //   map0: RemappingMap, cpts1: Array[State], views: ViewSet)
  //     : Array[ReducedComponentView] = {
  //   // The components corresponding to the new cross references
  //   val newCRs = newCrossRefs(map0, cpts1, preCpts)
  //   if(newCRs.nonEmpty){
  //     // extending the previous map has created new cross references, so
  //     // add another MissingCrossReferences object
  //     // println(
  //     //   "old map = "+Remapper.show(map0)+ // "\nmap = "+Remapper.show(map)+
  //     //     "\noriginal cpts = "+StateArray.show(inducedTrans.cv.components)+
  //     //     "\ncpts = "+StateArray.show(cpts)+
  //     //     "\npreCpts = "+StateArray.show(inducedTrans.preCpts)+
  //     //     "\nnewCRs = "+newCRs.map(StateArray.show).mkString("; "))
  //     val crossRefViews = // the views for the new  cross refs
  //       newCRs.map(Remapper.mkReducedComponentView(servers,_))
  //     MissingCrossReferences.sort(crossRefViews.filter(!views.contains(_)))
  //   }
  //   else EmptyReducedComponentView // Array[ReducedComponentView]()
  // }

  override def toString = {
    s"$trans\n operating on $cv\n induces $cv \n== "+
      s"(${trans.pre.servers}, ${StateArray.show(oldCpts)})\n -> "+
      s"(${trans.post.servers}, ${StateArray.show(newCpts)})\n== $newView"
  }
}

// =======================================================

object InducedTransitionInfo{
  /** Shared empty result from newMissingCrossRefs. */
  private val EmptyReducedComponentView = Array[ReducedComponentView]()

  /** The new missing cross reference views corresponding to inducedTrans,
    * formed by extending map0 so as to produce cpts1. */
  def newMissingCrossRefs(inducedTrans: InducedTransitionInfo, 
    map0: RemappingMap, cpts1: Array[State], views: ViewSet)
      : Array[ReducedComponentView] = {
    // The components corresponding to the new cross references
    val newCRs = newCrossRefs(map0, cpts1, inducedTrans.preCpts)
    if(newCRs.nonEmpty){
      // extending the previous map has created new cross references, so
      // add another MissingCrossReferences object
      // println(
      //   "old map = "+Remapper.show(map0)+ // "\nmap = "+Remapper.show(map)+
      //     "\noriginal cpts = "+StateArray.show(inducedTrans.cv.components)+
      //     "\ncpts = "+StateArray.show(cpts)+
      //     "\npreCpts = "+StateArray.show(inducedTrans.preCpts)+
      //     "\nnewCRs = "+newCRs.map(StateArray.show).mkString("; "))
      val crossRefViews = // the views for the new  cross refs
        newCRs.map(Remapper.mkReducedComponentView(inducedTrans.servers,_))
      MissingCrossReferences.sort(crossRefViews.filter(!views.contains(_)))
    }
    else EmptyReducedComponentView // Array[ReducedComponentView]()
  }


  /** Cross references between cpts and preCpts, or vice versa, where the
    * relevant parameter of cpts is not in the range of map.  Here cpts is
    * created by an extension of map, so any such cross reference was caused
    * by map being extended. */
  @inline private 
  def newCrossRefs(map: RemappingMap, cpts: Array[State], preCpts: Array[State])
      : Array[Array[State]] = {
    /* Is pid in the range of map? */
    @inline def inMap(pid: ProcessIdentity) = map(pid._1).contains(pid._2)
    var result = List[Array[State]](); var i = 0
    while(i < cpts.length){
      val c1 = cpts(i); i += 1
      val newId = !inMap(c1.componentProcessIdentity) // cross refs to c1 are new
      if(! contains(preCpts, c1)){
        var j = 0
        while(j < preCpts.length){
          val c2 = preCpts(j); j += 1
          if(! contains(cpts, c2)){
            // Cross reference from cpts to preCpts
            if(c1.hasIncludedParam(c2.family, c2.id) &&
                !inMap(c2.componentProcessIdentity))
              result ::= StateArray(Array(c1,c2))
            // Cross reference from preCpts to cpts
            if(newId && c2.hasIncludedParam(c1.family, c1.id))
              result ::= StateArray(Array(c2,c1))
          }
        }
      }
    }
    result.toArray
  }
}

// ==================================================================

import RemappingExtender.CandidatesMap
import RemapperP.Remapper

/** Information about missing cross references.  missingViews contains
  * component views that are necessary to satisfy condition (b) of the induced
  * transition corresponding to inducedTrans: all must be added to the
  * ViewSet. commonMissingPids is the common missing identities for condition
  * (c).  The view in inducedTrans was produced by renaming via map.
  * candidates stores values that undefined values in map might be mapped to;
  * but might be null if map is total.*/
class MissingCrossReferences(
  val inducedTrans: InducedTransitionInfo,
  missingViews: Array[ReducedComponentView],
  val map: RemappingMap, candidates: CandidatesMap,
  val commonMissingPids: Array[ProcessIdentity]
){
  assert(missingViews.nonEmpty && missingViews.forall(_ != null)) 
  // Check sorted
  for(i <- 0 until missingViews.length-1) 
    assert(missingViews(i).compare(missingViews(i+1)) < 0)
  // At most, a reference from each component of pre to each component of cv,
  // and vice versa: 3*2*2:
  assert(missingViews.length <= 12, "missingViews.length = "+missingViews.length)

  /** Check that map is defined over cv. */
  def checkMap = 
    for(t <- 0 until numTypes)
      require(map(t).length == inducedTrans.cv.getParamsBound(t),
        "\n map = "+Remapper.show(map)+"\ncv = "+inducedTrans.cv)

  checkMap

  @inline def isNewViewFound(views: ViewSet) = inducedTrans.isNewViewFound(views)

  /** Index of the next element of missingViews needed. */
  private var mvIndex = 0

  /** The first missing view, against which this should be registered. */
  def missingHead = synchronized{ missingViews(mvIndex) }

  /** Is this complete? */
  @inline def done = 
    synchronized{ mvIndex == missingViews.length || inducedTrans.isNewViewFound }

  /** Update missingViews and mvIndex based on the addition of cv.  cv is
    * expected to match the next missing view. */
  def updateMissingViewsBy(cv: ComponentView, views: ViewSet) = synchronized{
    // Is following TOCTTOU? 
    require(mvIndex < missingViews.length && missingViews(mvIndex) == cv,
      s"mvIndex = $mvIndex, cv = $cv, missingViews = \n"+
        missingViews.mkString("\n"))
    mvIndex += 1
    while(mvIndex < missingViews.length && 
      (missingViews(mvIndex) == null || views.contains(missingViews(mvIndex)))
    )
      mvIndex += 1
  }

  /** All total maps associated with this. */
  def allCompletions: ArrayBuffer[RemappingMap] = synchronized{
    if(candidates == null){
      // map should be total in this case
      for(t <- 0 until numTypes; i <- 0 until map(t).length) 
        assert(map(t)(i) >= 0)
      ArrayBuffer(map)
    }
    // val map1 = RemapperP.Remapper.cloneMap(map)
    // I don't think cloning is necessary.  map is private to this, and
    // protected by the synchronized block
    else RemappingExtender.allCompletions(map, candidates, inducedTrans.trans)
  }


}

// =======================================================

object MissingCrossReferences{
  /** Sort missingViews, removing duplicates. */
  def sort(missingViews: Array[ReducedComponentView])
      : Array[ReducedComponentView] = {
    // Use insertion sort, as the array is small.
    var i = 1 // Inv: sorted missingViews[0..i)
    while(i < missingViews.length){
      val mv = missingViews(i); var j = i; i += 1; assert(mv != null)
      // Inv missingViews[j+1..i) > mv; missingViews(j) is a duplicate or
      // equals mv, so missingViews[0..j)++missingViews[j+1..i)++[mv] is a
      // permutation of missingViews[0..i) at the start of this iteration.
      while(j > 0 && 
          (missingViews(j-1) == null || mv.compare(missingViews(j-1)) < 0)){
        missingViews(j) = missingViews(j-1); j -= 1
      }
      // Copy mv into position, unless duplicted by missingViews(j-1)
      if(j == 0 || missingViews(j-1) != mv) missingViews(j) = mv
      else missingViews(j) = null
    }
    // IMPROVE following
    missingViews.filter(_ != null)
  }




}
