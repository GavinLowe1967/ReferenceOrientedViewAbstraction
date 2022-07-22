package ViewAbstraction

import scala.collection.mutable.{ArrayBuffer,Map}
import java.util.concurrent.atomic.AtomicInteger

/** An object representing the events in a particular FDR session. */
class FDREvents(fdrSession: FDRSession) extends EventPrinter{


  /** Map giving the String for each event number. */
  private val eventStringMap = Map[Int, String]()

  /** Given internal representation of event, get corresponding String. */
  def eventToString(n: Int): String = eventStringMap(n)


  /** Map giving the event number for a String representing an event. */
  private val stringEventMap = Map[String, Int]()

  /** Get internal representation of event represented as String. 
    * Note: not thread-safe. */
  def eventToInt(st: String): Int = 
    try{ stringEventMap(st) }  // IMPROVE
    catch{  
      case _: java.util.NoSuchElementException =>
        println("eventToInt: Event not found: "+st); sys.exit()
    }


  /** Initialise eventStringMap and stringEventMap.
    * @param eventsSize the number of events (including tau and tick) plus one.
    */
  def initEvents(eventsSize: Int) = {
    println("Initialising events.")
    // Something like following is necessary or else uncompileEvent barfs.
    fdrSession.evalProc("let P_ = error -> STOP within P_[[ error <- e_ | e_ <- Events ]]")
    println(s"Logging events ($eventsSize events).")
    assert(eventStringMap.isEmpty && stringEventMap.isEmpty)
    val eventIndex = new AtomicInteger(1) // Next event to handle
    val ChunkSize = 100 // Each task is ChunkSize events
    // A single worker
    def worker = {
      var done = false
      // Store own results in following
      val myEs = new ArrayBuffer[Int](); val mySts = new ArrayBuffer[String]()
      var myIndex = eventIndex.getAndAdd(ChunkSize)
      while(myIndex < eventsSize){
        for(e <- myIndex until (myIndex+ChunkSize min eventsSize)){
          val st = fdrSession.uncompileEvent(e) // session.uncompileEvent(e).toString() // sequential bottleneck
          myEs += e; mySts += st; if(e%5000 == 0) print(".")
        }
        myIndex = eventIndex.getAndAdd(ChunkSize)
      } 
      // Copy into shared maps; this is quite fast.
      synchronized{ 
        for(i <- 0 until myEs.length){
          val e = myEs(i); val st = mySts(i)
          eventStringMap += e -> st; stringEventMap += st -> e
        }
      }
    } // end of worker 
    // session is a sequential bottleneck, so no gain in lots of workers.
    Concurrency.runSystem(4, worker)
    println()
  } 



}
