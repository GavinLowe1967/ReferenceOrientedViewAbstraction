package ViewAbstraction

import uk.ac.ox.cs.fdr._
// import scala.collection.JavaConverters._
import scala.jdk.CollectionConverters._
import scala.collection.mutable.{Map,ArrayBuffer}
// import scala.collection.parallel.CollectionConverters._
import java.util.concurrent.atomic.AtomicInteger

/** An object that creates an FDR session, and offers various operations on
  * it. 
  * @param fname the name of the file. */
class FDRSession(fname: String){
  /** The FDR Session object. */
  private val session = new Session

  session.loadFile(fname)

  /** The Cancellor, used in queries on the session. */
  private val canceller = new Canceller

  // Evaluation of non-process values. 

  /** Use the FDR session to evaluate the expression st. */ 
  def eval(st: String): String =
    session.evaluateExpression(st, canceller).result

  /** Convert internal representation of event into the corresponding 
    * String. */
  def uncompileEvent(event: Int): String =
    session.uncompileEvent(event).toString()

  /** Convert String representing event into internal representation. */
  private def compileEvent(st: String): Int =
    session.compileEvent(st, canceller).result.toInt

  /** Convert a String, representing a set, into a list of Strings. 
    * 
    * Note: avoid calling this on type names; use getTypeValues, instead. */
  def setStringToList(st: String): List[String] = {
    val xs = session.evaluateIterableExpression(st, canceller)
    xs.result.asScala.toList
  }

  /** String defining take and drop functions. */
  private val takeDropString =
    "let take(xs_, n_) = "+
      "if n_ == 0 or null(xs_) then <> else <head(xs_)>^take(tail(xs_), n_-1) "+
      "within let drop(xs_, n_) = "+
      "if n_ == 0 or null(xs_) then xs_ else drop(tail(xs_), n_-1) within "

  /** Convert a String, representing an FDR sequence, into a list of Strings.
    *  
    * Note: the list being evaluated should be bound to an FDR name, to avoid
    * is being repeatedly evaluated.  It's not clear that this is ever more
    * efficient. */
  def listStringToList(st: String): List[String] = {
    // We split the list into chunks of size chunk, and evaluate each chunk
    // separately, to avoid the apparent O(n^2) behaviour of
    // evaluateIterableExpression.
    val Chunk = 1000
    val length = eval(s"length($st)").toInt
    val result = new ArrayBuffer[String](); var i = 0
    while(i < length){
      val thisChunkString = takeDropString+s"take(drop($st, $i), $Chunk)"
      val thisChunk =
        session.evaluateIterableExpression(thisChunkString, canceller).result
      result ++= thisChunk.asScala
      i += Chunk
    }
    print(result.length)
    result.toList
  }

  /** Convert a String, representing an FDR sequence of sequences xss, into a
    * list of strings, representing the elements of concat (map f yss), where
    * yss is a permutation of xss.  */
  def seqSeqStringToList(st: String, f: String => String): Array[String] = {
    // Note: the following also evaluates st, which can be expensive.
    // However, st needs to be evaluated anyway, so there doesn't seem much to
    // be gained by avoiding this.
    val length = eval(s"length($st)").toInt; print(s"($length chunks.)")
    val result = new ArrayBuffer[String]() // holds result
    // Index into the sequence
    val nextIndex = new AtomicInteger(0)

    // A single worker
    def worker = {
      var done = false; val myResult = new ArrayBuffer[String]()
      do{
        val myIndex = nextIndex.getAndIncrement
        if(myIndex < length){
          val thisChunkString = f(s"nth_($st, $myIndex)")
          print(".")
          val thisChunk =
            session.evaluateIterableExpression(thisChunkString, canceller).
              result.asScala
          myResult ++= thisChunk
        }
        else done = true
      } while(!done);
      result.synchronized{ result ++= myResult }
    }

    Concurrency.runSystem(numThreads min length, worker)

    print(result.length); result.toArray
  }

  /** Does st represent a sequence of type <<a>>? */
  private def isSeqSeq(st: String): Boolean = {
    // Ugh!
    try{ 
      // The following throws an exception if st does not represent a sequence
      // of type <<a>>; otherwise it returns "false" (even if st is empty).
      eval(s"false and null(head($st))"); true
    }
    catch{ case _: Exception =>  false }
  }

  /** If st represents a sequence, evaluate f(st); if st represents a sequence
    * of sequences, evaluate concat(map f xss). */
  def evalSeqSeqOrSeq(st: String, f: String => String): Array[String] = {
    if(isSeqSeq(st)) seqSeqStringToList(st, f)
    else setStringToList(f(st)).toArray 
  }

  /** Does g represent a map that can be applied to x? */
  def isMapApp(g: String, x: String): Boolean = {
    try{ eval(s"if false then < mapLookup($g, $x) > else <>"); true }
    catch{ case _: Exception => false }
  }

  /** Evaluate the expression f(g(x)), where g is either an FDR Map or an FDR
    * function. */ 
  def applyFunctionOrMap[A](f: String => A, g: String, x: String): A = {
    if(isMapApp(g, x)) f(s"mapLookup($g, $x)") else f(s"$g($x)") 
  }

  /** Int representing the value st from the symmetry sub-type. */
  def symmetryValue(st: String): Int =
    session.symmetryValue(st, canceller).result.toInt

  /** Number of visible events. */
  def numEvents = eval("card(Events)").toInt

  // StringList to use in evalProc
  private val types = new StringList

  /** The values in a type; memoized in getTypeValues. */
  private val typeValues = Map[String, List[String]]()

  /** Get the values in a type. */
  def getTypeValues(typeName: String): List[String] = 
    typeValues.getOrElseUpdate(typeName, setStringToList(typeName))

  /** Get and record the type that includes the subtype typeName. */
  def getSuperType(typeName: String) = {
    val typeValues = getTypeValues(typeName)
    val superType = session.typeOfExpression(typeValues.head).result
    types.add(superType)
    superType
  }

  /** Get the name of the type represented by t. */
  def typeName(t: Long): String =
    session.symmetryTypeName(java.math.BigInteger.valueOf(t))


  // ======== Events and processes

  /** Get the int representing type typeName internally.
    * @param procName the name of a process parameterised by typeName, so 
    * procName(x) is a valid process for each x in typeName. */
  def getTypeInt(typeName: String): Long = {
    val tVals = getTypeValues(typeName)
    println(typeName+" -> "+tVals)
    def proc(x: String) =
      "let P_(x_) = error -> if x_ == "+x+" then SKIP else STOP within P_("+x+")"
    val machine = evalProc(proc(tVals.head))
    val variableVals = machine.variableValues(machine.rootNode).asScala.toList
    assert(variableVals.length == 1)
    variableVals.head.getType.longValue
    // This is a little inefficient, as we re-build this machine later.
    // val machine = evalProc(procName+"("+tVals.head+")")
    // val root = machine.rootNode
    // val variableVals = machine.variableValues(root).asScala.toList
    // // assert(variableVals.length == 1, variableVals.map(_.getValue.intValue))
    // assert(vv1.head.getType.longValue == variableVals.head.getType.longValue)
    // variableVals.head.getType.longValue
  }

  /** Use FDR to evaluate process expression st.
    * Pre: an earlier call to getSuperType initialised types. */
  def evalProc(st: String): Machine =
    session.evaluateProcessForSymmetry(
      st, SemanticModel.Traces, types,  canceller).result

  // /** Map giving the String for each event number. */
  // private val eventStringMap = Map[Int, String]()

  // /** Given internal representation of event, get corresponding String. */
  // def eventToString(n: Int): String = eventStringMap(n)

  // /** Map giving the event number for a String representing an event. */
  // private val stringEventMap = Map[String, Int]()

  // /** Get internal representation of event represented as String. 
  //   * Note: not thread-safe. */
  // def eventToInt(st: String): Int = 
  //   try{ stringEventMap(st) }  // IMPROVE
  //   catch{  
  //     case _: java.util.NoSuchElementException =>
  //       println("eventToInt: Event not found: "+st); sys.exit()
  //   }

  // /** Initialise eventStringMap and stringEventMap.
  //   * @param eventsSize the number of events (including tau and tick) plus one.
  //   */
  // def initEvents(eventsSize: Int) = {
  //   println("Initialising events.")
  //   // Something like following is necessary or else uncompileEvent barfs.
  //   evalProc("let P_ = error -> STOP within P_[[ error <- e_ | e_ <- Events ]]")
  //   println(s"Logging events ($eventsSize events).")
  //   assert(eventStringMap.isEmpty && stringEventMap.isEmpty)
  //   val eventIndex = new AtomicInteger(1) // Next event to handle
  //   val ChunkSize = 100 // Each task is ChunkSize events
  //   // A single worker
  //   def worker = {
  //     var done = false
  //     // Store own results in following
  //     val myEs = new ArrayBuffer[Int](); val mySts = new ArrayBuffer[String]()
  //     var myIndex = eventIndex.getAndAdd(ChunkSize)
  //     while(myIndex < eventsSize){
  //       for(e <- myIndex until (myIndex+ChunkSize min eventsSize)){
  //         val st = session.uncompileEvent(e).toString() // sequential bottleneck
  //         myEs += e; mySts += st; if(e%5000 == 0) print(".")
  //       }
  //       myIndex = eventIndex.getAndAdd(ChunkSize)
  //     } 
  //     // Copy into shared maps; this is quite fast.
  //     synchronized{ 
  //       for(i <- 0 until myEs.length){
  //         val e = myEs(i); val st = mySts(i)
  //         eventStringMap += e -> st; stringEventMap += st -> e
  //       }
  //     }
  //   } // end of worker 
  //   // session is a sequential bottleneck, so no gain in lots of workers.
  //   Concurrency.runSystem(4, worker)
  //   println()
  // } 

  /** Delete the underlying session, to free up memory. */
  def delete = session.delete

}
