package ViewAbstraction
import ox.gavin.profiling.Profiler

/* Objects stored in sets inside Views, recording information about previous
 * induced transitions.  
 * 
 * Each ServersReducedMap represents:
 * 
 * 1. the servers of the post-state of the transition2; 
 * 
 * 2. part of the remapping map (with newEffectOn, the result-defining map);
 * 
 * 3. the post states of the unified components that change state.
 * 
 * They are used in ComponentView.doneInducedPostServerRemaps and
 * ComponentView.conditionBInducedMap. 
 * 
 * Note: item 3 is currently not used.  This is controlled by
 * DetectRepeatRDMapWithUnification. */

object ServersReducedMap{
  /** Type representing the range restriction of a RemappingMap.  The
    * representation is described in Remapper.scala. */
  type ReducedMap = Array[Long]  

  /** Factory method for ServersReducedMaps. */
  def apply(servers: ServerStates, map: ReducedMap, newCpts: List[State] = null)
      : ServersReducedMap = {
    assert(newCpts == null) 
    Profiler.count("ServersReducedMap"+map.length)
    // With lazySet bound 44: 0 -> 6; 1 -> 2.3B; 2 -> 51.5M; 3 -> 1.6K 
    if(map.isEmpty) new ServersReducedMap0(servers)
    else if(map.length == 1) new ServersReducedMap1(servers, map(0))
    else if(map.length == 2) new ServersReducedMap2(servers, map(0), map(1))
    else new ServersReducedMapN(servers, map)
  }
}

// ==================================================================

import ServersReducedMap.ReducedMap

/** A class of objects used to key the doneInducedPostServersRemaps mapping in
  * each ComponentView. */
abstract class ServersReducedMap{
  /** Combine h and l: used in creating hashCodes. */
  @inline protected def combine(h: Int, l: Long) =
    (h*7) ^ l.toInt ^ (l >> 32).toInt

  @inline protected def hashCpts(newCpts: List[State]) = 
    if(newCpts == null) 0 else newCpts.hashCode

}

// ==================================================================

/** A ServersReducedMap corresponding to an empty map. */
class ServersReducedMap0(
  val servers: ServerStates /*, val newCpts: List[State] = null*/)
    extends ServersReducedMap{
  override def equals(that: Any) = that match{
    case srm: ServersReducedMap0 => 
      srm.servers == servers // && srm.newCpts == newCpts
    case _: ServersReducedMap => false
  }

  override def hashCode = servers.hashCode // ^ hashCpts(newCpts)

  override def toString = s"ServersReducedMap0($servers)" // , $newCpts
}

// ==================================================================

/** A ServersReducedMap whose map is a single Long. */
class ServersReducedMap1(val servers: ServerStates, val map: Long)
    extends ServersReducedMap{
  override def equals(that: Any) = that match{
    case srm: ServersReducedMap1 => 
      srm.servers == servers && srm.map == map 
    case _: ServersReducedMap => false
  }

  override def hashCode = combine(servers.hashCode, map)

  override def toString = s"ServersReducedMap1($servers, $map)"
}

// ==================================================================

/** A ServersReducedMap whose map is two Longs. */
class ServersReducedMap2(
  val servers: ServerStates, val map1: Long, val map2: Long)
    extends ServersReducedMap{
  override def equals(that: Any) = that match{
    case srm: ServersReducedMap2 => 
      srm.servers == servers && srm.map1 == map1  && srm.map2 == map2
    case _: ServersReducedMap => false
  }

  override def hashCode = combine(combine(servers.hashCode, map1), map2)

  override def toString = s"ServersReducedMap1($servers, $map1, $map2)"
}


// ==================================================================

/** A ServersReducedMap whose map contains at least three Longs. */
class ServersReducedMapN(val servers: ServerStates, val map: ReducedMap)
    extends ServersReducedMap{
  require(map.length > 2)

  override def equals(that: Any) = that match{
    case srm: ServersReducedMapN =>
      srm.servers == servers && srm.map.sameElements(map)
    case _: ServersReducedMap => false
  }

  override val hashCode = mkHash

  /** Make the hash function. */
  private def mkHash = {
    // In FP terms: foldl combine servers.hashCode map
    var h = servers.hashCode; var i = 0
    while(i < map.length){ h = combine(h, map(i)); i += 1 }
    h
  }

  override def toString = 
    s"ServersReducedMapN($servers, ${map.mkString(", ")})" // , $newCpts
}

// It might be worth having a case for exactly two Longs.

// IMPROVE: it would be better to omit the newCpts field when null.
