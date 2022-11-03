package ViewAbstraction

/** Support for a bit map representing a set of identities. */
object IdentitiesBitMap{
  /** Each bit map will be represented by a value of this type. */
  type IdentitiesBitMap = Long

  // Note: maybe we could use an Int here.

  /** Maximum number of identities allowed. */
  private val MaxIds = 64

  /** A bit map representing the empty set. */
  private val Empty = 0L

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
    assert(n <= MaxIds, s"Too many identities in script: max $MaxIds allowed.") 
  }

  /** The index (bit number) corresponding to the process identity (t,id). */
  @inline private def index(t: Type, id: Identity) = {
    require(id >= 0); offsets(t)+id
  }

  /** The bit mask corresponding to (t,id). */
  @inline private def mask(t: Type, id: Identity): Long = 1L << index(t,id)

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

}
