package ViewAbstraction

/** Objects that record information about which views might be added later.
  * Abstractly it stores pairs (missing, nv) for missing a set of views and nv
  * a view.  If all the views in missing are added, then nv can also be
  * added.  
  * 
  * These are added in effectOn when a transition pre -> post induces a
  * transition cv -> nv, but where the views in missing represent combinations
  * of components from pre and cv that are not yet in the store. */ 
trait EffectOnStore{
  /** Add the pair (missing, nv) to the store. */
  def add(missing: List[ComponentView], nv: ComponentView): Unit

  type MissingInfo = (List[ComponentView], ComponentView)

  /** Get all pairs (missing, nv) in the store with cv in missing. */
  def get(cv: ComponentView): List[MissingInfo] 

  def size: Int
}

// =======================================================

import scala.collection.mutable.HashMap

class SimpleEffectOnStore extends EffectOnStore{
  /** The underlying store.  For each pair (missing, nv) in the abstract set,
    * and for each cv in missing, store(cv) contains (missing, nv). */
  private val store = 
    new HashMap[ComponentView, List[MissingInfo]]

  /** Add the pair (missing, nv) to the store. */
  def add(missing: List[ComponentView], nv: ComponentView): Unit = {
    for(cv <- missing){
      val prev = store.getOrElse(cv, List[MissingInfo]())
      if(!prev.contains((missing,nv))) store += cv -> ((missing,nv)::prev)
    }
  }

  /** Get all pairs (missing, nv) in the store with cv in missing. */
  def get(cv: ComponentView): List[MissingInfo] =
    store.getOrElse(cv, List[MissingInfo]())

  def size = store.size
}
