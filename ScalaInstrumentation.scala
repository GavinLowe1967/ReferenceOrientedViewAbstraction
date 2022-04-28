import scala.collection.mutable.{Stack,Map,Set}
import java.lang.reflect.Modifier
import ox.gavin.profiling.MemoryProfiler
import MemoryProfiler.traverse
import ViewAbstraction._


class ScalaInstrumentation{

  /** Main function. */ 
  def apply(args: Array[String]) = {
    // println(MemoryProfiler.getSize(Array.fill(1000)(new AnyRef)))
    // Gives 4016 or 8024, depending on whether 32 or 64 bit refs are used,
    // which corresponds to whether there is less than or at least 32GB of
    // heap.
    for(arg <- args) println(arg)
    var fname = ""; var i = 0; 
    var singleRef = false // ; var newEffectOn = false
    var bound = Int.MaxValue
    while(i < args.length) args(i) match{
      case "--singleRef" => singleRef = true; i += 1
      // case "--newEffectOn" => newEffectOn = true; i += 1
      case "--bound" => bound = args(i+1).toInt; i += 2
      case fn => fname = fn; i += 1
    }

    assert(fname.nonEmpty)
    VA.check(fname, bound, singleRef)
  }

}

