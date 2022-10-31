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
  // Array.fill(numWorkers)(new Array[BitMap](BMPoolCapacity))

  /** The number of items in the pool foreach thread. */
  private var bitmapPoolSize: Array[Int] = null // Array.fill(numWorkers)(0)

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
  private val RowPoolCapacity = 50

  /** The pool of rows of remapping rows, flattened to reduce memory
    * accesses. The pool for thread `me` for rows of size `size` are in entry
    * `indexFor(me, size)`. */
  private var rowPool: Array[Pool[Row]] = null

  /** The index in rowPool and rowPoolSize for thread `me` for rows of
    * size `size`. */
  @inline private def indexFor(me: Int, size: Int) = me*(maxRowSize+1)+size

  /** The number of rows available in each pool, indexed as for rowPool. */
  private var rowPoolSize: Array[Int] = null

  /* For each index i, the Rows in rowPool(i)[0..rowPoolSize(i)) are
   * available. */

  /** Get a remapping row of size `size`.  Note: the initial state of the row is
    * undefined: client code is responsible for initialisation. */
  def getRemappingRow(size: Int): Row = { 
    val me = ThreadID.get 
    Profiler.count(s"Pools.getRemappingRow")
    val pIndex = indexFor(me,size); val index = rowPoolSize(pIndex)-1
    if(index >= 0){ rowPoolSize(pIndex) = index; rowPool(pIndex)(index) }
    else mkArray(size) // new Array[Int](size)
// IMPROVE: above non-inlining for profiling purposes
  }

  private def mkArray(size: Int) = new Array[Int](size)

  /** Return the rows of map to the row pool. */
  def returnRemappingRows(map: RemappingMap): Unit = {
    // return
    val me = ThreadID.get; var i = 0
    while(i < map.length){
      val row = map(i); i += 1; val size = row.size
      Profiler.count(s"Pools.returnRemappingRow")
      val pIndex = indexFor(me,size); val index = rowPoolSize(pIndex)
      if(index < RowPoolCapacity){
        rowPool(pIndex)(index) = row; rowPoolSize(pIndex) = index+1
      }
      else Profiler.count(s"Pools.returnRemappingRow failed")
    }
    returnRemappingMap(map) 
  }

  /** Clone row. */
  def cloneRow(row: Row): Row = {
    val newRow = getRemappingRow(row.size); var j = 0
    while(j < row.size){ newRow(j) = row(j); j += 1 }
    newRow
  }

  // -------------------------------------------- A pool for RemappingMaps

  /** Maximum number of RemappingMaps stored per worker. */
  private val MapPoolCapacity = 50

  /** A pool of RemappingMaps. */
  private var mapPool: Array[Pool[RemappingMap]] = null

  /** The number of RemappingMaps stored for each worker. */
  private var mapPoolSize: Array[Int] = null

  /** Get a RemappingMap. */
  def getRemappingMap: RemappingMap = {
    val me = ThreadID.get
    Profiler.count(s"Pools.getRemappingMap")
    val index = mapPoolSize(me)-1
    if(index >= 0){ mapPoolSize(me) = index; mapPool(me)(index) }
    else new Array[Array[Int]](numTypes)
  }

  /** Return map to the pool. */
  @inline private def returnRemappingMap(map: RemappingMap) = {
    val me = ThreadID.get
    Profiler.count(s"Pools.returnRemappingMap")
    val index = mapPoolSize(me)
    if(index < MapPoolCapacity){
      mapPool(me)(index) = map; mapPoolSize(me) = index+1
    }
    else Profiler.count(s"Pools.returnRemappingMap failed")
  }

  /** Produce a (deep) clone of map. */
  @inline def cloneMap(map: RemappingMap): RemappingMap = {
    val map1 = getRemappingMap; var t = 0 
    while(t < numTypes){ map1(t) = cloneRow(map(t)); t += 1 }
    map1
  }


  // -------------------------------------------------------

  /** Initialise the pools.  This needs to be called before a repeated check.
    * Called by FDREvents.fdrTypeToType, when typeSizes are known. */
  def init(typeSizes: Array[Int]) = {
    // remapping rows
    maxRowSize = 2*typeSizes.max+2
    rowPool =
      Array.fill(numWorkers*(maxRowSize+1))(new Pool[Row](RowPoolCapacity))
    rowPoolSize = Array.fill(numWorkers*(maxRowSize+1))(0)
    // RemappingMaps
    mapPool = Array.fill(numWorkers)(new Pool[RemappingMap](MapPoolCapacity))
    mapPoolSize = Array.fill(numWorkers)(0)
    // bitmaps
    bitmapPool = Array.fill(numWorkers)(new Pool[BitMap](BMPoolCapacity))
    bitmapPoolSize = Array.fill(numWorkers)(0)
  }

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
