package ViewAbstraction

/** Support for maps over process identities, implemented using flattening,
  * either into a single array, or into a bit map. */
object Flatten{
  /** The offsets corresponding to each type: each entry is the sum of sizes of
    * earlier types. */
  private var offsets: Array[Int] = null

  /** Initialise the offsets.  Called from System.  Note: all of typeSizes must
    * be set first. */
  def init(typeSizes: Array[Int]) = {
    var n = 0; offsets = new Array[Int](numTypes)
    for(t <- 0 until numTypes){
      assert(typeSizes(t) > 0)
      offsets(t) = n; n += typeSizes(t)
    }
  }

  /** The index (bit number) corresponding to the process identity (t,id). */
  @inline def index(t: Type, id: Identity) = {
    require(id >= 0 && id < typeSizes(t)); offsets(t)+id
  }
}

// ==================================================================

/** Support for a bit map representing a set of identities. */
object IdentitiesBitMap{
  /** Each bit map will be represented by a value of this type. */
  type IdentitiesBitMap = Long

  // Note: maybe we could use an Int here.

  /** Maximum number of identities allowed. */
  private val MaxIds = 64

  /** A bit map representing the empty set. */
  val Empty = 0L

  //import Flatten.index

  /** Check that we can handle types with combined size typeSizesSum.  Called
    * from System.  */
  def init(typeSizesSum: Int) = 
    assert(typeSizesSum <= MaxIds,
      s"Too many identities in script: max $MaxIds allowed.")

  /** The bit mask corresponding to (t,id). */
  @inline private def mask(t: Type, id: Identity): IdentitiesBitMap =
    1L << Flatten.index(t,id)

  /** Get the value in bm corresponding to (t,id). */
  @inline def get(bm: IdentitiesBitMap, t: Type, id: Identity): Boolean = 
    (bm & mask(t,id)) != 0

  @inline def apply(bm: IdentitiesBitMap, t: Type, id: Identity): Boolean =
    get(bm, t, id)

  /** bm updated to add (t,id). */
  @inline def set(bm: IdentitiesBitMap, t: Type, id: Identity)
      : IdentitiesBitMap =
    bm | mask(t,id)

  /** A bit map holding the identities of cpts. */
  def makeIdsBitMap(cpts: Array[State]): IdentitiesBitMap = {
    var bm = Empty; var i = 0
    while(i < cpts.length){
      val (f,id) = cpts(i).componentProcessIdentity; bm = set(bm, f, id); i += 1
    }
    bm
  }

  def toArrayBitMap(bm: IdentitiesBitMap): BitMap = {
    val newIds = Array.tabulate(numTypes)(t => new Array[Boolean](typeSizes(t)))
    for(t <- 0 until numTypes; id <- 0 until newIds(t).length)
      if(get(bm, t, id)) newIds(t)(id) = true
    newIds
  }
}

// ==================================================================

import scala.reflect.ClassTag

/** Support for maps over process identities, implemented as a flattened
  * array. */
object FlatArrayMap{
  /** The total number of identities.  Each map is of this size. */
  private var size = -1

  /** Initialise.  Maps will be created of size theSize. */
  def init(theSize: Int) = size = theSize

  type FlatArrayMap[A] = Array[A]

  /** Get a new map of type A. */
  def getMap[A](implicit tag: ClassTag[A]) = new Array[A](size)

  import Flatten.index

  /** Get the value in map corresponding to (t,id). */
  @inline def get[A](map: FlatArrayMap[A], t: Type, id: Identity): A = 
    map(index(t,id))

  /** Set the value in map(t,id) to x. */
  @inline def set[A](map: FlatArrayMap[A], t: Type, id: Identity, x: A) =
    map(index(t,id)) = x

  /** Flatten a two-dimensional map into a FlatArrayMap. */ 
  def from2D[A](map2D: Array[Array[A]])(implicit tag: ClassTag[A])
      : FlatArrayMap[A] = {
    var map = getMap[A]
    for(t <- 0 until numTypes; id <- 0 until typeSizes(t))
      set(map, t, id, map2D(t)(id))
    map
  }
}

// ==================================================================

/** Support for representing a subset of [0..8) as a bit map within a Byte. */
object ByteBitMap{
  /** Each set is represented by a ByteBitMap, with the ith bit set to indicate
    * the presence of i. */
  type ByteBitMap = Byte

  /** Representation of the empty set. */
  val Empty: ByteBitMap = 0.asInstanceOf[Byte]

  /** Bit mask for entry i. */
  @inline private def mask(i: Int) = { require(0 <= i && i < 8); 1<<i }

  /** Is i in the set represented by b? */
  @inline def get(b: ByteBitMap, i: Int): Boolean = (b & mask(i)) != 0

  /** The set corresponding to b with i added. */
  @inline def set(b: ByteBitMap, i: Int): ByteBitMap = 
    (b | mask(i)).asInstanceOf[Byte]

  /** The set containing the values in a.  */
  @inline def fromArray(a: Array[Int]): ByteBitMap = {
    var b = Empty; for(i <- a) b = set(b,i); b
  }

  /** The set containing the values in list. */
  @inline def fromList(list: List[Int]): ByteBitMap = {
    var b = Empty; for(i <- list) b = set(b,i); b
  }

  /** An iterator over the entries in b. */
  def iterator(b: ByteBitMap) = new Iterator[Int]{
    private var ix = 0

    @inline private def advance() = while(ix < 8 && !get(b,ix)) ix += 1

    advance()

    def hasNext = ix < 8

    def next() = { val res = ix; ix += 1; advance(); res }
  }

}
