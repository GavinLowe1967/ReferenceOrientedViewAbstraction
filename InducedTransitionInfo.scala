package ViewAbstraction

import RemapperP.Remapper

/** Information about an induced transition.  This corresponds to transition
  * trans = pre -e-> post inducing
  * cv == (pre.servers, oldCpts) -> (post.servers, newCpts) == newView.  
  * oldCpts might be null, in which case it is set later. */
class InducedTransitionInfo(
  val newView: ReducedComponentView, val trans: Transition,
  // oldCpts: Array[State], 
  val cv: ComponentView
){
  require(trans.pre.components.length <= 3 && cv.components.length <= 2)
  require(trans.pre.servers == cv.servers)

  @inline def oldCpts: Array[State] = null

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
    v.setCreationInfoIndirect(trans, oldCpts, cv) // , newCpts)
    v
  }

  /** An InducedTransitionInfo extending this, instantiating oldCpts with
    * cpts. */
  def extend(cpts: Array[State]) = {
    require(oldCpts == null)
    new InducedTransitionInfo1(newView, trans, cpts, cv) 
  }

  /** The common missing references associated with this. */
  def commonMissingRefs =
    SingleRefEffectOnUnification.commonMissingRefs(preCpts, oldCpts).toArray

  override def toString = {
    s"$trans\n operating on $cv\n induces $cv \n== "+
      s"(${trans.pre.servers}, "+
      (if(oldCpts == null) "<null>" else StateArray.show(oldCpts))+
      s")\n -> $newView"
    // s"(${trans.post.servers}, ${StateArray.show(newCpts)})\n== $newView"
  }
}

// ==================================================================

class InducedTransitionInfo1(
  newView: ReducedComponentView, trans: Transition,
  override val oldCpts: Array[State], cv: ComponentView)
    extends InducedTransitionInfo(newView, trans, cv){
  require(oldCpts != null)
}

// =======================================================

object InducedTransitionInfo{
  /** Factory method. */
  def apply(newView: ReducedComponentView, trans: Transition,
    oldCpts: Array[State], cv: ComponentView)
      : InducedTransitionInfo =
    if(oldCpts != null) new InducedTransitionInfo1(newView, trans, oldCpts, cv)
    else new InducedTransitionInfo(newView, trans, cv)


  // /** Shared empty result from newMissingCrossRefs. */
  // private val EmptyReducedComponentView = Array[ReducedComponentView]()

  // /** The new missing cross reference views corresponding to inducedTrans,
  //   * formed by extending map0 so as to produce cpts1. */
  // def newMissingCrossRefs(inducedTrans: InducedTransitionInfo, 
  //   map0: RemappingMap, cpts1: Array[State], views: ViewSet)
  //     : Array[ReducedComponentView] = 
  //   newMissingCrossRefs(
  //     map0, inducedTrans.servers, cpts1, inducedTrans.preCpts, views)
 
  // /** The new missing cross reference views caused by extending map0 so as to
  //   * produce cpts1.  This corresponds to a transition starting with
  //   * (servers,preCpts), acting on (servers,cpts1). */
  // private def newMissingCrossRefs(map0: RemappingMap, servers: ServerStates,
  //   cpts1: Array[State], preCpts: Array[State], views: ViewSet)
  //     : Array[ReducedComponentView] = {
  //   // The components corresponding to the new cross references
  //   val newCRs = newCrossRefs(map0, cpts1, preCpts)
  //   if(newCRs.nonEmpty){
  //     // extending the previous map has created new cross references
  //     val crossRefViews = // the views for the new  cross refs
  //       newCRs.map(Remapper.mkReducedComponentView(servers,_))
  //     MissingCrossReferences.sort(crossRefViews.filter(!views.contains(_)))
  //   }
  //   else EmptyReducedComponentView // Array[ReducedComponentView]()
  // }

  // /** Cross references between cpts and preCpts, or vice versa, where the
  //   * relevant parameter of cpts is not in the range of map.  Here cpts is
  //   * created by an extension of map, so any such cross reference was caused
  //   * by map being extended. */
  // @inline private 
  // def newCrossRefs(map: RemappingMap, cpts: Array[State], preCpts: Array[State])
  //     : Array[Array[State]] = {
  //   /* Is pid in the range of map? */
  //   @inline def inMap(pid: ProcessIdentity) = map(pid._1).contains(pid._2)
  //   var result = List[Array[State]](); var i = 0
  //   while(i < cpts.length){
  //     val c1 = cpts(i); i += 1
  //     val newId = !inMap(c1.componentProcessIdentity) // cross refs to c1 are new
  //     if(! contains(preCpts, c1)){
  //       var j = 0
  //       while(j < preCpts.length){
  //         val c2 = preCpts(j); j += 1
  //         if(! contains(cpts, c2)){
  //           // Cross reference from cpts to preCpts
  //           if(c1.hasIncludedParam(c2.family, c2.id) &&
  //               !inMap(c2.componentProcessIdentity))
  //             result ::= StateArray(Array(c1,c2))
  //           // Cross reference from preCpts to cpts
  //           if(newId && c2.hasIncludedParam(c1.family, c1.id))
  //             result ::= StateArray(Array(c2,c1))
  //         }
  //       }
  //     }
  //   }
  //   result.toArray
  // }
}
