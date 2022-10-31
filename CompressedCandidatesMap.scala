package ViewAbstraction

/** A compressed representation of a set of values by which an entry in a map
  * can be extended. */
object CompressedCandidatesMap{
  /** For each parameter x, the candidates to which x can be remapped must be in
    * the range [0..MaxCands). */
  val MaxCands = 15

  /** The representation of the values that a particular parameter can be mapped
    * to.  A non-negative value represents a subset of [0..MaxCands) as a bit
    * map.  A negative value x represents that the map is defined at that
    * position, with value x with the most significant bit cleared. */
  type Candidates = Short

  /** The set of all values in the range [0..MaxCands). */
  private val All: Candidates = ((1<<MaxCands)-1).asInstanceOf[Candidates]

  /** The empty set. */
  val Empty: Candidates = 0.asInstanceOf[Candidates]

  /** Check that i is in the appropriate range. */
  @inline private def check(i: Int) = 
    require(0 <= i && i < MaxCands, s"Too many parameters in a view: $i")
  // Note: failures of the above can be fixed by using a larger type for
  // Candidates.

  /** The mask corresponding to just i. */
  @inline private def mask(i: Int): Candidates = {
    check(i); (1<<i).asInstanceOf[Candidates]
  }

  /** The set of candidates cs with i added. */
  @inline def add(cs: Candidates, i: Int): Candidates = 
    (cs | mask(i)).asInstanceOf[Candidates]

  /** The set of candidates cs with i removed. */
  @inline def remove(cs: Candidates, i: Int): Candidates = 
    (cs & (All-mask(i))).asInstanceOf[Candidates]

  /** The set [0..i). */
  @inline def allUpTo(i: Int): Candidates = {
    check(i); ((1<<i)-1).asInstanceOf[Candidates]
  }

  /** The list of values represented by cs, in increasing order. */
  @inline def toList(cs: Candidates): List[Int] = 
    if(cs < 0) List() // fixed value
    else {
      var result = List[Int](); var i = MaxCands
      while(i > 0){ i -= 1; if((cs & mask(i)) != 0) result ::= i }
      result
    }

  /** Just the most significant bit set. */
  private val MSB = (1<<MaxCands)

  /** The encoding of a fixed mapping to i. */
  @inline def fixed(i: Int): Candidates = {
    check(i); (i | MSB).asInstanceOf[Candidates]
  }

  /** Bit mask with all bits except the most significant set. */
  private val Mask = MSB-1

  /** The inverse of fixed, decoding the representation of a fixed mapping. */
  @inline private def decodeFixed(cs: Candidates): Int = {
    require(cs < 0); val i = cs & Mask; check(i); i
  }

  /** The compressed representation of a set of RemappingMaps. */
  type CompressedCandidatesMap = Array[Candidates]

  /** An unflattened version, with separate rows corresponding to different
    * types. */
  type UnflattenedCandidatesMap = Array[Array[Candidates]]

  /** The map corresponding to candidates: for each encoding of a value x, the
    * corresponding x; otherwise undefined.  */
  @inline def extractMap(candidates: UnflattenedCandidatesMap): RemappingMap = 
    candidates.map(_.map(cs => if(cs < 0) decodeFixed(cs) else -1))

  /** Split `candidates` into separate arrays of size `sizes`. */
  @inline def splitBy(candidates: CompressedCandidatesMap, sizes: Array[Int])
      : UnflattenedCandidatesMap = {
    require(candidates.length == sizes.sum)
    val result = new Array[Array[Candidates]](sizes.length); var offset = 0
    for(i <- 0 until sizes.length){
      val end = offset+sizes(i); result(i) = candidates.slice(offset, end)
      offset = end
    }
    result
  }

}
