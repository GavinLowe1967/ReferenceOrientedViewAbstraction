package ViewAbstraction

import collection.MyHashSet
import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}

/** Object to calculate the effect of the transition trans on cv.  Create
  * extra views caused by the way the transition changes cv, and add them to
  * nextNewViews. */
class EffectOn(
  trans: Transition, cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
{
  /* Overview of main function.
   * 
   * apply
   * |--EffectOnUnification.apply
   * |--processInduced
   * |  |--getCrossRefs
   * |  |--processInducedInfo
   */

  import Unification.UnificationList //  = List[(Int,Int)]
  import EffectOnUnification.InducedInfo

  protected val pre = trans.pre; protected val post = trans.post
  protected val postCpts = post.components;

  private val highlight = 
    Transition.highlight(trans) && {
      // [107(N0) || 109(N1) || 110() || 114(T0) || 119() || 1()] ||
      // [31(T1,N2,N3,N1) || 10(N2,Null,N3)]
      val princ = cv.components(0)
      princ.cs == 31 && princ.ids.sameElements(Array(1,2,3,1)) && {
        val second = cv.components(1)
        second.cs == 10 && second.ids.sameElements(Array(2,-1,3))
      }
    }

  if(highlight) println(s"\nEffectOn($trans,\n  $cv)")

  require(pre.servers == cv.servers) // && pre.sameComponentPids(post)

  override def toString = s"EffectOn($trans, $cv)"

  /** What does cpt get mapped to given unifications unifs? */
  protected def getNewPrinc(cpt: State, unifs: UnificationList): State = {
    var us = unifs; while(us.nonEmpty && us.head._1 != 0) us = us.tail
    if(us.isEmpty) cpt else postCpts(us.head._2)
  }
  
  import EffectOn.views

  //protected var sreou: SingleRefEffectOnUnification = null

  /** The effect of the transition t on cv.  Create extra views caused by the
    * way the transition changes cv, and add them to nextNewViews. */
  def apply() : Unit = {
    // Early bail-out if servers don't change, no chance of unification with
    // components that change state, and no chance of secondary induced
    // transitions.  This captures over about 25% of cases with lazySet.csp,
    // bound 44; nearly all other cases have servers that change state.
    if(trans.mightGiveSufficientUnifs(cv)){
      // inducedInfo: ArrayBuffer[(RemappingMap, Array[State],
      // UnificationList, ReducedMap)] is a set of tuples (pi, pi(cv.cpts),
      // unifs, reducedMap) where pi is a unification function corresponding
      // to unifs.
      val inducedInfo: InducedInfo = EffectOnUnification.combine(trans, cv)
      processInduced(inducedInfo)
    }
  }

  /** Process the information about induced transitions with full views. */
  @inline private 
  def processInduced(inducedInfo: InducedInfo) = {
    require(!singleRef); var index = 0
    while(index < inducedInfo.length){
      val (map, unifs) = inducedInfo(index); index += 1
      Profiler.count("EffectOn step "+unifs.isEmpty)
      val cpts = Remapper.applyRemapping(map, cv.components)
      val newPrinc = getNewPrinc(cpts(0), unifs)
      var newComponentsList =
        StateArray.makePostComponents(newPrinc, postCpts, cpts)
      processInducedInfo(cpts, unifs, newComponentsList)
      Pools.returnRemappingRows(map)
    } // end of while loop
  }

  /** Process induced information in the case of full views. */
  private def processInducedInfo(cpts: Array[State], unifs: UnificationList,
    newComponentsList: List[Array[State]])
      : Unit = {
    require(!singleRef)
    for(newComponents <- newComponentsList){
      val nv = Remapper.mkComponentView(post.servers, newComponents)
      Profiler.count("newViewCount") 
      if(!views.contains(nv)){
        if(nextNewViews.add(nv)) addedView(cpts, newComponents, nv, unifs)
        else // nv was in nextNewViews 
          showRedundancy(
            nextNewViews.get(nv), cpts, newComponents, nv, unifs, true)
      } // end of if(!views.contains(nv))
      // Try to work out why so many cases are redundant
      else // views already contains nv
        showRedundancy(views.get(nv), cpts, newComponents, nv, unifs, true)
    } // end of for loop
  }

  // ----------- Various helper functions

  /** Actions performed when a new view has been added to the view set,
    * principally setting the creation information. */
  @inline private def addedView(
    cpts: Array[State], newComponents: Array[State], nv: ComponentView,
    unifs: UnificationList) 
  = {
    if(highlight) println("added")
    Profiler.count("addedViewCount")
    if(showTransitions || ComponentView0.highlight(nv))
      showTransition(cpts, newComponents, nv, unifs)
    nv.setCreationInfoIndirect(trans, cpts, cv) // , newComponents)
    checkRepresentable(nv)
  }

  /** Show the transition. */
  @inline protected def showTransition(
    cpts: Array[State], newComponents: Array[State], nv: ComponentView, 
    unifs: UnificationList, isPrimary: Boolean = true)
  = println(s"$trans\n  with unifications $unifs, isPrimary == $isPrimary\n"+
    "  induces "+
    EffectOnStore.showInduced(cv, cpts, post.servers, newComponents, nv)
  )

  /** Show information about a redundancy. */
  @inline protected def showRedundancy(
    v1: => ComponentView, cpts: Array[State], newComponents: Array[State], 
    nv: ComponentView, unifs: UnificationList, isPrimary: Boolean)
  = {
    Profiler.count("EffectOn redundancy:"+isPrimary+unifs.isEmpty)
    if(showRedundancies && v1.inducedFrom(cv)){
      showTransition(cpts, newComponents, nv, unifs, isPrimary)
      println(s"Previously "+v1.showCreationInfo+"\n")
    }
  }

  /** Check that nv is representable using the identities in the script. */
  @inline protected def checkRepresentable(nv: ComponentView) = 
    if(!nv.representableInScript){
      println("Not enough identities in script to combine transition\n"+
        s"$pre -> \n  $post and\n$cv.  Produced view\n"+nv.toString0)
      sys.exit()
    }
}

// ==================================================================


/** Supporting functions for EffectOn objects, and encapsulation of the
  * EffectOnStore. */
object EffectOn{
  /** The current set of views.  Set by init. */
  var views: ViewSet = null
// IMPROVE: protect

  /** The system.  Set by init. */
  private var system: SystemP.System = null

  def init(views: ViewSet, system: SystemP.System) = {
    this.views = views; this.system = system
  }


}
