package ViewAbstraction

import scala.collection.mutable.{ArrayBuffer,Map}
import java.util.concurrent.atomic.AtomicInteger

/** An object representing the events in a particular FDR session. */
class FDREvents(fdrSession: FDRSession, superTypeNames: Array[String])
    extends EventPrinter{
  /* Main public functions:
   * Events: initEvents, eventToString, eventToInt, numEvents
   * Types: getIdRemap, getNameMap, fdrTypeToType
   */

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

  /** Number of visible events. */
  def numEvents = fdrSession.eval("card(Events)").toInt

  /** Initialise eventStringMap and stringEventMap.
    * @param eventsSize the number of events (including tau and tick) plus one.
    */
  def initEvents(eventsSize: Int) = {
    println("Initialising events.")
    // Something like following is necessary or else uncompileEvent barfs.
    val p = "let P_ = error -> STOP within P_[[ error <- e_ | e_ <- Events ]]"
    fdrSession.evalProc(p)
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
          val st = fdrSession.uncompileEvent(e) // sequential bottleneck
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

  // ========= Information about types

  /* The various maps related to types (idRemaps, theNameMap, theTypeMap) are
   * initialised via calls to fdrTypeToType for each type, from Components.
   * This is before the transition systems themselves are created. */

  /** A map for a particular supertype, mapping, for each element x of that
    * supertype, the representation of x inside FDR to the representation used
    * here; elements of the subtype map onto an initial segment of the
    * naturals, and other (distinguished) values map onto negative ints. */
  private type IdRemap = Map[Int, Int]

  /** A map giving an IdRemap for each type, indexed by the representation of
    * the types inside FDR. */
  private val idRemaps = Map[Long, IdRemap]() 

  /** An IdRemap for the type corresponding to t in FDR; for each element x of
    * that type, it maps the representation of x inside FDR to the
    * representation used here. */
  def getIdRemap(t: Long): IdRemap = idRemaps(t)

  /** A map for a particular type, mapping from the representation used here to
    * the name from the script. */
  private type NameMap = Map[Identity, String]

  /** A map giving a NameMap for each type. */
  private val theNameMap = Map[Type, NameMap]()

  /** The NameMap, mapping from the representation used here to the name from
    * the script.  Called after the transition system is built. */
  def getNameMap = theNameMap

  /** Mapping from non-distinguished value names to their corresponding
    * representation. */
  private val fromNameMap = Map[String, Parameter]()

  /** The internal representation of the non-distinguished value with name
    * `st`. */
  def fromName(st: String): Parameter = fromNameMap(st)

  /** Map from the Longs used to represent types in FDR to the Ints used here.  
    * The latter are in the range [0..numTypes). 
    * 
    * The entry for type t is built by typeMap, the first time a parameter of
    * this type is encountered. */
  private val theTypeMap = Map[Long, Int]()

  /** Given the Long used to represent a type within FDR, return the
    * corresponding Int used here.  Also, if this is the first time we've seen
    * this type, calculate and store information about the type, updating
    * theTypeMap, fdrTypeIds, idRemaps and typeSizes.  */
  def fdrTypeToType(t: Long): Type = theTypeMap.get(t) match{
    case Some(i) => i
    case None =>
      // This is the first time we've encountered this type
      val superTypeName = fdrSession.typeName(t)
      val i = superTypeNames.indexOf(superTypeName); assert(i >= 0)
      val typeName = familyTypeNames(i)
      println(s"$superTypeName: $t; $i; $typeName")
      theTypeMap += t -> i 
      val idRemap = Map[Int, Int]() // FDR reps => values used here
      val nameMap = Map[Int, String]() // values used here => script names
      // Values in the type and supertype
      val superTypeVals = fdrSession.getTypeValues(superTypeName)
      val typeValues = fdrSession.getTypeValues(typeName)
      // Next ints to use for ids and distinguished values
      var nextId = 0; var nextDistinguished = -1
      // Build the mapping for each value of superType in turn.
      for(st <- superTypeVals){
        val id = fdrSession.symmetryValue(st) // Int representing st inside FDR
        if(typeValues.contains(st)){ 
          // println(s"$st => ($i, $nextId)")
          idRemap += id -> nextId; fromNameMap += st -> (i,nextId); nextId += 1 
        }
        else{ idRemap += id -> nextDistinguished; nextDistinguished -= 1 }
        nameMap += idRemap(id) -> st
        println(s"$id: $st -> ${idRemap(id)}")
      }
      val typeSize = nextId // # non-distinguished values
      idRemaps += t -> idRemap; theNameMap += i -> nameMap;
      assert(typeSize <= MaxTypeSize, s"Type $superTypeName has too many values")
      typeSizes(i) = typeSize; superTypeSizes(i) = idRemap.size
      distinguishedSizes(i) = superTypeSizes(i) - typeSize
      println("Supertype size = "+idRemap.size)
      println("Distinguished values = "+distinguishedSizes(i))
      Pools.init(typeSizes)
      i
  }

  /** Characters that can be separators between fields in an event. */
  private val Separators = ".(){},<>|=> ".toArray

  /** Is c a separator between fields in an event? */
  private def isSeparator(c: Char) = Separators.contains(c)

  /** Remap e, replacing every field in froms with the corresponding field in
    * tos. */
  def remapEvent(e: EventInt, froms: Array[Parameter], tos: Array[Parameter])
      : EventInt = {
    // Convert arguments to string form
    val fromsLength = froms.length; require(tos.length == fromsLength)
    val eString = eventToString(e)
    val fromStrings = froms.map{ case (t,id) => theNameMap(t)(id) }
    val toStrings = tos.map{ case (t,id) => theNameMap(t)(id) }
    // Parse e, splitting at Separators
    val builder = new scala.collection.mutable.StringBuilder()
    var i = 0; val len = eString.length
    while(i < len){
      // get next field
      var j = i; while(j < len && !isSeparator(eString(j))) j += 1
      val thisField = eString.substring(i,j); var k = 0 
      // search for thisField in fromStrings
      while(k < fromsLength && fromStrings(k) != thisField) k += 1
      if(k < fromsLength) builder ++= toStrings(k) else builder ++= thisField 
      // Get the separators
      i = j; while(j < len && isSeparator(eString(j))) j += 1
      val seps = eString.substring(i,j); builder ++= seps; i = j
    }
    eventToInt(builder.toString)
  }

}
