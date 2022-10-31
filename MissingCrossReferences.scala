package ViewAbstraction

import scala.collection.mutable.ArrayBuffer
import RemapperP.Remapper
import ox.gavin.profiling.Profiler

/** Information about an induced transition.  This corresponds to transition
  * trans = pre -e-> post inducing
  * cv == (pre.servers, oldCpts) -> (post.servers, newCpts) == newView.*/
class InducedTransitionInfo(
  val newView: ReducedComponentView, val trans: Transition,
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
      : Array[ReducedComponentView] = 
    newMissingCrossRefs(
      map0, inducedTrans.servers, cpts1, inducedTrans.preCpts, views)
 
  /** The new missing cross reference views caused by extending map0 so as to
    * produce cpts1.  This corresponds to a transition starting with
    * (servers,preCpts), acting on (servers,cpts1). */
  def newMissingCrossRefs(map0: RemappingMap, servers: ServerStates,
    cpts1: Array[State], preCpts: Array[State], views: ViewSet)
      : Array[ReducedComponentView] = {
    // The components corresponding to the new cross references
    val newCRs = newCrossRefs(map0, cpts1, preCpts)
    if(newCRs.nonEmpty){
      // extending the previous map has created new cross references
      val crossRefViews = // the views for the new  cross refs
        newCRs.map(Remapper.mkReducedComponentView(servers,_))
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
import CompressedCandidatesMap.CompressedCandidatesMap
import RemapperP.Remapper

/** Information about missing cross references.  `missingViews` contains
  * component views that are necessary to satisfy condition (b) of the induced
  * transition corresponding to inducedTrans: all must be added to the
  * ViewSet. 
  * 
  * With lazyNewEffectOn, this corresponds to a set of remappings captured by
  * `candidates`.  But `candidates` might be null if there are no common missing
  * references, in which case `inducedTrans.cpts` is non-null.  Also
  * `commonMissingPids = null` in this case.
  * 
  * With !lazyNewEffectOn, `commonMissingPids` is the common missing
  * identities for condition (c).  In this case, candidates = null and
  * `commonMissingPids != null`. */
class MissingCrossReferences(
  val inducedTrans: InducedTransitionInfo,
  private val missingViews: Array[ReducedComponentView],
  val candidates: CompressedCandidatesMap,
  val commonMissingPids: Array[ProcessIdentity]
){
  assert(missingViews.nonEmpty && missingViews.forall(_ != null)) 
  // Check sorted
  for(i <- 0 until missingViews.length-1) 
    assert(missingViews(i) < missingViews(i+1))
  // At most, a reference from each component of pre to each component of cv,
  // and vice versa: 3*2*2:
  assert(missingViews.length <= 12, "missingViews.length = "+missingViews.length)
  // Certain fields are set null to save memory
  if(lazyNewEffectOnStore){
    assert(commonMissingPids == null)
    // We set cpts xor candidates
    assert(inducedTrans.cpts == null ^ candidates == null)
    if(candidates != null) 
      assert(candidates.length == inducedTrans.cv.getParamsBound.sum,
        "candidates = "+candidates.mkString(",")+"\nsizes = "+
          inducedTrans.cv.getParamsBound.mkString(","))
  }
  else assert(inducedTrans.cpts != null  && candidates == null)
  Profiler.count("MissingCrossReferences:"+(candidates == null)) 

  @inline def isNewViewFound(views: ViewSet) = inducedTrans.isNewViewFound(views)

  /** Has this been superseded by another MissingCrossReferences with the same
    * newView and a subset of the missingViews? */
  private var superseded = false

  def setSuperseded = superseded = true

  def isSuperseded = superseded

  /** Index of the next element of missingViews needed. */
  private var mvIndex: Short = 0

  @inline private def incMvIndex = mvIndex = (mvIndex+1).asInstanceOf[Short]

  /** The first missing view, against which this should be registered. */
  def missingHead = synchronized{ missingViews(mvIndex) }

  /** Is this complete? */
  @inline def done = 
    synchronized{ mvIndex == missingViews.length || inducedTrans.isNewViewFound }

  /** Is this complete? */
  @inline def done(views: ViewSet) = synchronized{ 
    mvIndex == missingViews.length || inducedTrans.isNewViewFound(views)
  }

  /** Update missingViews and mvIndex based on the addition of cv.  cv is
    * expected to match the next missing view. */
  def updateMissingViewsBy(cv: ComponentView, views: ViewSet) = synchronized{
    // Is following TOCTTOU? 
    require(mvIndex < missingViews.length && missingViews(mvIndex) == cv,
      s"mvIndex = $mvIndex, cv = $cv, missingViews = \n"+
        missingViews.mkString("\n"))
    incMvIndex // mvIndex += 1
    while(mvIndex < missingViews.length && 
      (missingViews(mvIndex) == null || views.contains(missingViews(mvIndex)))
    )
      incMvIndex // mvIndex += 1
  }

  /** All total maps associated with this. */
  def allCompletions: ArrayBuffer[RemappingMap] = synchronized{
    require(candidates != null)
    RemappingExtender.allCompletions(
      null, candidates, inducedTrans.cv, inducedTrans.trans)
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

  /** Result type for the compare function. */
  type Comparison = Int

  /** Possible results from compare. */
  val Subset = 0; val Equal = 1; val Superset = 2; val Incomparable = 3

  /** Compare the missingViews of mcr1 and mcr2.  Return Subset if those of mcr1
    * are a subset of those for mcr2.  Similar for Equal, Superset and
    * Incomparable. */
// IMPROVE: pass in ViewSet, and ignore views already found
  def compare(mcr1: MissingCrossReferences, mcr2: MissingCrossReferences)
      : Comparison = {
    require(mcr1.inducedTrans.newView == mcr2.inducedTrans.newView)
    val mv1 = mcr1.missingViews; val mv2 = mcr2.missingViews
    val len1 = mv1.length; val len2 = mv2.length
    // Note: we use the fact that mv1, mv2 are sorted
    var i1: Int = mcr1.mvIndex; var i2: Int = mcr2.mvIndex
    // Inv: mv1[0..i1) == mv2[0..i2), ignoring found values
    while(i1 < len1 && i2 < len2 && mv1(i1) == mv2(i2)){ i1 += 1; i2 += 1 }
    if(i1 == len1){ if(i2 == len2) Equal else Subset }
    else if(i2 == len2) Superset
    else if(mv1(i1) < mv2(i2)){
      // mv1 is not a subset of mv2; test if mv2 is a subset of mv1.  Inv:
      // mv2[0..i2) is a subset of mv1[0..i1); mv1[0..i1) < mv2[i2..len2).
      while(i1 < len1 && mv1(i1) < mv2(i2)) i1 += 1
      // Additional inv: mv1(i1) >= mv2(i2) or i1 = len1 or i2 = len2
      while(i1 < len1 && i2 < len2 && mv1(i1) == mv2(i2)){
        i1 += 1; i2 += 1
        if(i2 < len2) while(i1 < len1 && mv1(i1) < mv2(i2)) i1 += 1
      }
      if(i2 == len2) Superset else Incomparable
    }
    else{
      // mv2 is not a subset of mv1; test if mv1 is a subset of mv2.  Inv:
      // mv1[0..i1) is a subset of mv2[0..i2); mv2[0..i2) < mv1[i1..len1).
      while(i2 < len2 && mv2(i2) < mv1(i1)) i2 += 1
      // Additional inv: mv2(i1) >= mv1(i1) or i1 = len1 of i2 = len2
      while(i1 < len1 && i2 < len2 && mv1(i1) == mv2(i2)){
        i1 += 1; i2 += 1
        if(i1 < len1) while(i2 < len2 && mv2(i2) < mv1(i1)) i2 += 1
      }
      if(i1 == len1) Subset else Incomparable
    }
  }
}