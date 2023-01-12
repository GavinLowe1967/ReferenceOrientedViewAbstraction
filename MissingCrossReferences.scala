package ViewAbstraction

import scala.collection.mutable.ArrayBuffer
import RemapperP.Remapper
import ox.gavin.profiling.Profiler

import RemappingExtender.CandidatesMap
import CompressedCandidatesMap.CompressedCandidatesMap

/** Information about missing cross references.  `missingViews` contains
  * component views that are necessary to satisfy condition (b) of the induced
  * transition corresponding to inducedTrans: all must be added to the
  * ViewSet. 
  * 
  * With lazyNewEffectOn, this corresponds to a set of remappings captured by
  * `candidates`.  In the superclass, candidates is null (and not explicitly
  * stored, to save memory), and `inducedTrans.cpts` is non-null.  */
class MissingCrossReferences(
  val inducedTrans: InducedTransitionInfo,
  private val missingViews: Array[ReducedComponentView],
  val conditionCSatisfied: Boolean
){
  @inline def candidates:  CompressedCandidatesMap = null

  // def conditionCSatisfied = candidates == null

  assert(missingViews.nonEmpty && missingViews.forall(_ != null)) 
  // Check sorted
  for(i <- 0 until missingViews.length-1) 
    assert(missingViews(i) < missingViews(i+1))
  // At most, a reference from each component of pre to each component of cv,
  // and vice versa: 3*2*2:
  assert(missingViews.length <= 12, "missingViews.length = "+missingViews.length)
  // Certain fields are set null to save memory.  We set cpts xor candidates
  assert(inducedTrans.cpts == null ^ candidates == null)
  Profiler.count("MissingCrossReferences:"+(candidates == null)+conditionCSatisfied) 

  @inline def isNewViewFound(views: ViewSet) = inducedTrans.isNewViewFound(views)

  /** Has this been superseded by another MissingCrossReferences with the same
    * newView and a subset of the missingViews? */
  private var superseded = false

  def setSuperseded = synchronized{ superseded = true }

  def isSuperseded = synchronized{ superseded }

  /** Index of the next element of missingViews needed. */
  private var mvIndex: Short = 0

  @inline private def incMvIndex = mvIndex = (mvIndex+1).toShort 

  /** The first missing view, against which this should be registered. */
  def missingHead = synchronized{ missingViews(mvIndex) }

  /** Have all the required views been marked as found? */
  @inline def allFound = mvIndex == missingViews.length

  /** Is this complete? */
  @inline def done = 
    synchronized{ allFound || inducedTrans.isNewViewFound }

  /** Is this complete? */
  @inline def done(views: ViewSet) = 
    synchronized{ allFound || inducedTrans.isNewViewFound(views) }

  /** Update missingViews and mvIndex based on the addition of cv.  cv is
    * expected to match the next missing view. */
  def updateMissingViewsBy(cv: ComponentView, views: ViewSet) = synchronized{
    // Is following TOCTTOU? 
    require(mvIndex < missingViews.length && missingViews(mvIndex) == cv,
      s"mvIndex = $mvIndex, cv = $cv, missingViews = \n"+
        missingViews.mkString("\n"))
    incMvIndex // mvIndex += 1
    while(mvIndex < missingViews.length && 
      (/*missingViews(mvIndex) == null ||*/ views.contains(missingViews(mvIndex)))
    )
      incMvIndex // mvIndex += 1
  }

  /** Remove all members of missingViews in views.  Called from NewEffectOnStore
    * while purging.  NOTE: this doesn't have a huge effect, affecting about
    * 1% of cases, so might not be worthwhile. */
  def updateMissingViews(views: ViewSet) = synchronized{
    // Note: views might contain missingViews(mvIndex), in which case it will
    // be dealt with on the next ply.  We avoid removing it.
    val len = missingViews.length
    if(mvIndex+1 < len){ // at least two elements
      var i = len; var j = len
      // Inv: we have checked all elements of missingViews[i..len), and
      // compacted them into positions [j..len).
      while(i > mvIndex+1){
        i -= 1; val mv = missingViews(i)
        if(!views.contains(mv)){ j -= 1; missingViews(j) = mv }
        else Profiler.count("updateMissingViews removed")
      }
      missingViews(j-1) = missingViews(mvIndex); mvIndex = (j-1).toShort
    }
  }

  /** All total maps associated with this. */
  def allCompletions: ArrayBuffer[RemappingMap] = synchronized{
    require(candidates != null)
    RemappingExtender.allCompletions(
      null, candidates, inducedTrans.cv, inducedTrans.trans)
  }

  override def toString = 
    s"MissingCrossReferences for\n$inducedTrans;\nmissingViews = "+
      missingViews.mkString("; ")

}

// ==================================================================

/** Information about missing cross references.  `candidates` captures a set of
  * mappings over inducedtrans.pre.  */
class MissingCrossReferencesCandidates(
  inducedTrans: InducedTransitionInfo,
  missingViews: Array[ReducedComponentView],
  override val candidates: CompressedCandidatesMap)
extends MissingCrossReferences(inducedTrans, missingViews, false){
  require(candidates != null)
  require(candidates.length == inducedTrans.cv.getParamsBound.sum,
    "candidates = "+candidates.mkString(",")+"\nsizes = "+
      inducedTrans.cv.getParamsBound.mkString(","))
}
// IMPROVE: can we avoid the parameter conditionCSatisfied in the superclass?
// It's always false.

// =======================================================

object MissingCrossReferences{
  /** Factory method. */
  def apply(inducedTrans: InducedTransitionInfo,
    missingViews: Array[ReducedComponentView],
    candidates: CompressedCandidatesMap, conditionCSatisfied: Boolean)
      : MissingCrossReferences = {
    assert(conditionCSatisfied == (candidates == null))
    if(candidates == null) 
      new MissingCrossReferences(inducedTrans, missingViews, conditionCSatisfied)
    else new MissingCrossReferencesCandidates(
      inducedTrans, missingViews, candidates)
  }


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

  /** Compare the requirements of mcr1 and mcr2 for conditions (b) and (c).
    * Return Subset if those of mcr1 are a subset of those for mcr2.  Similar
    * for Equal, Superset and Incomparable. 
    * 
    * The operation uses synchronized on both mcr1 and mcr2.  This is sound
    * providing either: (1) mcr1 is a new object, that no other thread has
    * access to, as is the case in calls from NewEffectOnStore.shouldStore; or
    * (2) no other thread will be accessing either object, as is the case
    * during calls from NewEffectOnStore.purgeByNewView.  */
// IMPROVE: pass in ViewSet, and ignore views already found
  def compare(mcr1: MissingCrossReferences, mcr2: MissingCrossReferences)
      : Comparison = mcr1.synchronized{ mcr2.synchronized{
    require(mcr1.inducedTrans.newView == mcr2.inducedTrans.newView)
    // require(mcr1.conditionCSatisfied && mcr2.conditionCSatisfied)
    // Perform case analysis on whether condition (c) is satisfied for each.
    if(mcr1.conditionCSatisfied){
      if(mcr2.conditionCSatisfied) compareMissingViews(mcr1, mcr2)
      else if(subset(mcr1, mcr2)) Subset else Incomparable 
        // compareMissingViews(mcr1, mcr2) match{
        // // IMPROVE: more specialised comparison?
        // case Subset | Equal => Subset 
        // case _ => Incomparable
        // }
    }
    else if(mcr2.conditionCSatisfied){
      if(subset(mcr2, mcr1)) Superset else Incomparable
    }
      // // mcr1's condition c requirements are a proper superset of mcr2's
      // compareMissingViews(mcr1, mcr2) match{
      //   case Superset | Equal => Superset
      //   case _ => Incomparable
      // }
    else Incomparable // neither satisfied, probably for different requirements
  }}

  /** Compare the missingViews of mcr1 and mcr2, i.e. the requirements for
    * condition (b). */
  @inline private def compareMissingViews(
    mcr1: MissingCrossReferences, mcr2: MissingCrossReferences)
      : Comparison = {
    val mv1 = mcr1.missingViews; val mv2 = mcr2.missingViews
    val len1 = mv1.length; val len2 = mv2.length
    // Note: we use the fact that mv1, mv2 are sorted
    var i1: Int = mcr1.mvIndex; var i2: Int = mcr2.mvIndex
    //   for(ix <- i1 until len1-1) assert(mv1(ix) < mv1(ix+1))
    //   for(ix <- i2 until len2-1) assert(mv2(ix) < mv2(ix+1))
    // Inv: mv1[0..i1) == mv2[0..i2), ignoring found values
    while(i1 < len1 && i2 < len2 && mv1(i1) == mv2(i2)){ i1 += 1; i2 += 1 }
    if(i1 == len1){ if(i2 == len2) Equal else Subset }
    else if(i2 == len2) Superset
    else if(mv1(i1) < mv2(i2)){
      // mv1 is not a subset of mv2; test if mv2 is a subset of mv1. 
      if(subset1(mv2, i2, len2, mv1, i1, len1)) Superset else Incomparable
      // Inv: mv2[0..i2) is a subset of mv1[0..i1); mv1[0..i1) <
      // mv2[i2..len2).
      // val ss = subset(mv2, i2, len2, mv1, i1, len1)
      // while(i1 < len1 && mv1(i1) < mv2(i2)) i1 += 1
      // // Additional inv: mv1(i1) >= mv2(i2) or i1 = len1 or i2 = len2
      // while(i1 < len1 && i2 < len2 && mv1(i1) == mv2(i2)){
      //   i1 += 1; i2 += 1
      //   if(i2 < len2) while(i1 < len1 && mv1(i1) < mv2(i2)) i1 += 1
      // }
      // assert(ss == (i2 == len2)) 
      // if(i2 == len2) Superset else Incomparable
    }
    else{
      // mv2 is not a subset of mv1; test if mv1 is a subset of mv2.  
      if(subset1(mv1, i1, len1, mv2, i2, len2)) Subset else Incomparable
      // Inv: mv1[0..i1) is a subset of mv2[0..i2); mv2[0..i2) <
      // mv1[i1..len1).
      // val ss = subset(mv1, i1, len1, mv2, i2, len2)
      // while(i2 < len2 && mv2(i2) < mv1(i1)) i2 += 1
      // // Additional inv: mv2(i1) >= mv1(i1) or i1 = len1 of i2 = len2
      // while(i1 < len1 && i2 < len2 && mv1(i1) == mv2(i2)){
      //   i1 += 1; i2 += 1
      //   if(i1 < len1) while(i2 < len2 && mv2(i2) < mv1(i1)) i2 += 1
      // }
      // assert(ss == (i1 == len1))
      // if(i1 == len1) Subset else Incomparable
    }
  }

  /** Is mv1[ix1..len1) a subset of mv2[ix2..len2) (or equal)? */
  @inline private def subset1(
    mv1: Array[ReducedComponentView], ix1: Int, len1: Int,
    mv2: Array[ReducedComponentView], ix2: Int, len2: Int)
      : Boolean = {
    // Note: here we avoid comparing ReducedComponentViews using "<", but just
    // test for reference equality.  We use the fact that the arrays are sorted. 
    var i1 = ix1; var i2 = ix2; val lenDiff = len2-len1
    // Inv: (1) mv1[ix1..i1) is a subset of mv2[ix2..i2); (2) if mv1[i1..len1)
    // is a subset of mv2[ix2..len2) then it is a subset of mv2[i2..len2).
    // We iterate only while len1-i1 <= len2-i2
    while(i1 < len1 && i2-i1 <= lenDiff){ // i2 < len2
      val v1 = mv1(i1); val limit = lenDiff+i1
      // Iterate only while len1-i1 <= len2-i2
      while(i2 <= limit && ! mv2(i2).eq(v1)) i2 += 1 
      if(i2 <= limit) i1 += 1
    }
    i1 == len1
/*
    if(ix1 == len1) true
    else{
      var i1 = ix1; var i2 = ix2
      // Inv: mv1[ix1..i1) is a subset of mv2[ix2..i2);
      // mv2[ix2..i2) < mv1[i1..len1)
      while(i2 < len2 && mv2(i2) < mv1(i1)) i2 += 1
      // Additional inv: mv2(i1) >= mv1(i1) or i1 = len1 of i2 = len2
      while(i1 < len1 && i2 < len2 && mv1(i1) == mv2(i2)){
        i1 += 1; i2 += 1
        if(i1 < len1) while(i2 < len2 && mv2(i2) < mv1(i1)) i2 += 1
      }
// IMPROVE: could bail out if len2-i2 < len1-i1
      i1 == len1
    }
 */
  }

  /** Are the missing views of mcr1 a subset of, or equal to, those of mcr2? */
  @inline private 
  def subset(mcr1: MissingCrossReferences, mcr2: MissingCrossReferences)
      : Boolean = {
    val mv1 = mcr1.missingViews; val mv2 = mcr2.missingViews
    subset1(mv1, mcr1.mvIndex, mv1.length, mv2, mcr2.mvIndex, mv2.length)
  }

}
