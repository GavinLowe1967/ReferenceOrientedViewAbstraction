package ViewAbstraction

/** Trait supporting sharing. */
abstract class Sharding(shards: Int){
  /** Bit shift to produce a value in [0..shards).  */
  protected val shardShift = {
    var s = shards; var ss = 0 // Inv shards = s * 2^ss
    while(s > 1){
      assert((s&1) == 0); s = s >>> 1; ss += 1
    }
    32-ss
  }

  /** The shard to use for a value with hash h; the most significant
    * bits of h. */
  @inline protected def shardFor(h: Int) = h >>> shardShift
}
