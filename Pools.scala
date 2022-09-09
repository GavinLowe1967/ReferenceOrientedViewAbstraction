package ViewAbstraction

import ox.gavin.profiling.Profiler

/** An object holding pools of various commonly used datatypes. */
object Pools{
  /** A pool of values of type A, for a particular thread. */
  private type Pool[A] = Array[A]

  /* Most variables below are initialised by init(). */

  // --------------------------------------------------- Pool of BitMaps

  /** The maximum number of BitMaps stored in any pool. */
  private val BMPoolCapacity = 20

  /** Pools of BitMaps, indexed by ThreadIDs. */
  private var bitmapPool: Array[Pool[BitMap]] = null
  // Array.fill(numThreads)(new Array[BitMap](BMPoolCapacity))

  /** The number of items in the pool foreach thread. */
  private var bitmapPoolSize: Array[Int] = null // Array.fill(numThreads)(0)

  /** Get a BitMap. */
  def getBitMap: BitMap = {
    val me = ThreadID.get; Profiler.count(s"Pools.getBitMap")
    val index = bitmapPoolSize(me)-1
    if(index >= 0){ bitmapPoolSize(me) = index; bitmapPool(me)(index) }
    else newBitMap
  }

  /** Return bm to the pool. */
  def returnBitMap(bm: BitMap) = {
    val me = ThreadID.get; Profiler.count(s"Pools.returnBitMap")
    val index = bitmapPoolSize(me)
    if(index < BMPoolCapacity){ 
      // clear bm
      for(t <- 0 until numTypes; i <- 0 until bm(t).length) bm(t)(i) = false
      bitmapPool(me)(index) = bm; bitmapPoolSize(me) = index+1 
    }
  }

  // -------------------------------------- A pool for rows of RemappingMaps.

  type Row = Array[Int]

  /** The maximum size of row stored in the pool. */
  private var maxRowSize = -1 // 2*typeSizes.max+2

  /** The max number of rows we store in any pool. */
  private val RowPoolCapacity = 30

  /** Pool of rows of remapping maps. rowPool(id)(n) contains rows of
    * size n for thread id. */
  private var rowPool: Array[Array[Array[Row]]] = null 
  // Array.fill(numThreads,maxRowSize+1)(new Array[Row](RowPoolCapacity))

  /** The number of rows available in each pool. */
  private var rowPoolSize: Array[Array[Int]] = null
  // Array.fill(numThreads,maxRowSize+1)(0)

  /* For each thread t and size size, the Rows in
   * rowPool(t)(size)[ 0 .. rowPoolSize(t)(size) ) are available. */

  /** Get a remapping row of size `size`. */
  def getRemappingRow(size: Int): Row = { 
    val me = ThreadID.get // ; assert(me < numThreads)
    Profiler.count(s"Pools.getRemappingRow($size)")
    // assert(size < rowPoolSize(me).length, size)
    val index = rowPoolSize(me)(size)-1
    if(index >= 0){ rowPoolSize(me)(size) = index; rowPool(me)(size)(index) }
    else Array.fill(size)(-1)
  }

  /** Return the rows of map to the row pool. */
  def returnRemappingRows(map: RemappingMap) = {
    val me = ThreadID.get; var i = 0
    while(i < map.length){
      val row = map(i); i += 1; val size = row.size
      Profiler.count(s"Pools.returnRemappingRow($size)")
      val index = rowPoolSize(me)(size)
      if(index < RowPoolCapacity){
        // Clear row
        var j = 0; while(j < size){ row(j) = -1; j += 1 }
        rowPool(me)(size)(index) = row; rowPoolSize(me)(size) = index+1
      }
      else Profiler.count(s"Pools.returnRemappingRow($size) failed")
    }
  }

  /** Clone row. */
  def cloneRow(row: Row): Row = {
    val newRow = getRemappingRow(row.size); var j = 0
    while(j < row.size){ newRow(j) = row(j); j += 1 }
    newRow
  }

  // -------------------------------------------------------

  /** Initialise the pools.  This needs to be called before a repeated check.
    * Called by FDREvents.fdrTypeToType, when typeSizes are known. */
  def init(typeSizes: Array[Int]) = {
    // remapping rows
    maxRowSize = 2*typeSizes.max+2
    rowPool =
      Array.fill(numThreads,maxRowSize+1)(new Pool[Row](RowPoolCapacity))
    rowPoolSize = Array.fill(numThreads,maxRowSize+1)(0)
    // bitmaps
    bitmapPool = Array.fill(numThreads)(new Pool[BitMap](BMPoolCapacity))
    // Array.fill(numThreads)(List[BitMap]())
    bitmapPoolSize = Array.fill(numThreads)(0)
  }

/*
  /** Pool of RemappingMaps. */
  private var remappingMapPool = List[RemappingMap]()

  /** Get a remapping map. */
  def getRemappingMap: RemappingMap = synchronized{
    Profiler.count("Pools.getRemappingMap")
    if(remappingMapPool.isEmpty) newRemappingMap
    else{ 
      val map = remappingMapPool.head; remappingMapPool = remappingMapPool.tail
      map 
    }
  }

  /** Return map to the pool. */
  def returnRemappingMap(map: RemappingMap) = synchronized{
    val me = ThreadID.get; Profiler.count("Pools.returnRemappingMap")
    // clear map
    for(t <- 0 until numTypes){
      assert(map(t).length == remappingMapTemplate(t).length)
      for(i <- 0 until map(t).length) map(t)(i) = -1
    }
    remappingMapPool ::= map
  }
 */
}


// ==================================================================


/** An object providing thread identifiers.
  * Based on Herlihy & Shavit, Section A.2.4 */
object ThreadID{
  /** The next thread ID to use */
  private var nextID = 0

  /** Get the next thread ID to use */
  private def getNextID = synchronized{  nextID += 1; nextID-1 }
  // println(s"getNextID $nextID");

  /** This thread's ID, as a thread-local object */
  private object ThreadLocalID extends ThreadLocal[Int]{
    override def initialValue(): Int = getNextID 
  }

  /** Get this thread's ID */
  def get: Int = ThreadLocalID.get

  /** Reset the next thread ID to use. 
    * Should be run only in a sequential setting. */
  def reset = nextID = 0
}
