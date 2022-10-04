package ViewAbstraction

import collection.MyHashSet
import ox.gavin.profiling.Profiler
import ViewAbstraction.RemapperP.Remapper
import scala.collection.mutable.{ArrayBuffer}

/** Object to calculate the effect of the transition trans on cv with
  * singleRef.  Create extra views caused by the way the transition changes
  * cv, and add them to nextNewViews. */
class SingleRefEffectOn(
  trans: Transition, cv: ComponentView, nextNewViews: MyHashSet[ComponentView])
    extends EffectOn(trans, cv, nextNewViews)
{



}
