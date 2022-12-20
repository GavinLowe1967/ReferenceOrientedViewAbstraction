package ViewAbstraction.collection

/** Object containing helper methods for maps where keys are deletable. */
object DeletableMap{
  /** Value representing an empty slot in hashes. */
  val Empty = 0    // = 000...0 binary

  /** Value representing a deleted slot in hashes. */
  val Deleted = -1 // = 111...1 binary

  /* If the hashCode of a key is either Empty or Deleted, we replace it by
   * EmptyProxy or DeletedProxy, respectively (flipping most significant
   * bit). */
  private val EmptyProxy = Empty ^ Int.MinValue     // = 1000...0 binary
  private val DeletedProxy = Deleted ^ Int.MinValue // = 0111...1 binary

  /** A hash for a; guaranteed not to be Empty or Deleted. */
  def hashOf[A](a: A): Int = {
    val h = scala.util.hashing.byteswap32(a.hashCode)  // a.hashCode
    if(h == Empty) EmptyProxy else if(h == Deleted) DeletedProxy else h 
  }

  /** Does the hash value h represent a used slot (neither Empty nor
    * Deleted)? */
  @inline def filled(h: Int) = h != Empty && h != Deleted
}
