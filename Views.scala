package ViewAbstraction

import scala.collection.mutable.Set
import ox.gavin.profiling.Profiler
import scala.math.Ordering.Implicits._ // for sorting list of lists


/** Various operations on views of ring processes. */
object Views{
  /** Views of a family of replicated processes. */
  type View = Array[State]

  assert(numTypes >= 0 && maxSubtypeSize >= 0 && numTypes*maxSubtypeSize <= 64,
         "Too many identities in script")

  def show(v: View): String = v.mkString("<", ", ", ">")

  def compare(v1: View, v2: View) = {
    val len = v1.length // ; assert(len == v2.length)
    var j = 0
    while(j < len && v1(j) == v2(j)) j += 1
    if(j == len) 0 else State.StateOrdering.compare(v1(j), v2(j))
  }

  // ========= Pools

  // /** Minimum size of views for which pools are stored. FIXME */
  // val MinViewPoolSize = 4

  // /** Maximum size of views for which pools are stored. */
  // val MaxViewSize = 7

  // /** Max number of views of each size to store. */
  // private var PoolSize = -1 

  // /** Factorial function! */
  // private def fact(n: Int): Int = if(n == 0) 1 else n*fact(n-1)

  // /** Set PoolSize based on cShapes. */
  // def setPoolSize(cShapes: List[Shape]) = {
  //   // A shape (n1,...,nm) gives rise to a possible n1!...nm! permutations.
  //   // We take the max over all shapes, and add a few (since threads hold a few
  //   // additional views in additional to all permutations).
  //   PoolSize = cShapes.map(_.map(fact).product).max + 8
  //   // println("PoolSize = "+PoolSize) 
  // }

  // /** A pool for Views, all of the same size. */
  // private class ViewPool(size: Int){
  //   var buff = new Array[View](PoolSize)
  //   var count = 0
  //   /* buff[0..count) stores Views for re-use. */

  //   /** Add v to this pool. */
  //   @inline def add(v: View) = 
  //     if(count < PoolSize){ buff(count) = v; count += 1 }
  //     // else  Profiler.count("ViewPool.add fail"+size)
  //     // else print("*")

  //   /** Get a View, either from the pool or a new one. */
  //   @inline def get: View = 
  //     if(count > 0){ count -= 1; buff(count) }
  //     // val vss = ThreadLocalViewPool.get; val vs = vss(size)
  //     // if(vs.nonEmpty){ vss(size) = vs.tail; vs.head }
  //     else new View(size) // { Profiler.count("ViewPool.get fail"+size); }
  // }

  // /** Thread-local pools of Views, indexed by size of Views. */
  // private object ThreadLocalViewPool extends ThreadLocal[Array[ViewPool]]{
  //   override def initialValue() = Array.tabulate(MaxViewSize+1)(new ViewPool(_))
  // }

  // /* IMPROVE: allow non-overlapping get, not requiring explicit return. */

  // /** Get a View of size size, maybe recycling an old one. */
  // @inline def newView(size: Int): View = 
  //   if(size < MinViewPoolSize) new View(size)
  //   else{
  //     val pools = ThreadLocalViewPool.get; pools(size).get
  //     // if(pool.count > 0){ pool.count -= 1; pool.buff(pool.count) }
  //     // val vss = ThreadLocalViewPool.get; val vs = vss(size)
  //     // if(vs.nonEmpty){ vss(size) = vs.tail; vs.head }
  //     // else{ /* Profiler.count("newViewFail"+size); */ new View(size) }
  //   }

  // /** Get a View containing elements of sts0, maybe recycling an old one. */
  // @inline def newView(sts0: List[State]): View = {
  //   var sts = sts0; val v = newView(sts.length); var i = 0
  //   while(sts.nonEmpty){ v(i) = sts.head; sts = sts.tail; i += 1 }
  //   v
  // }

  // /** Return v for recycling. */
  // @inline def returnView(v: View) = {
  //   if(v.length >= MinViewPoolSize){ // IMPROVE
  //     val pools = ThreadLocalViewPool.get; pools(v.length).add(v)
  //     // if(pool.count < PoolSize){ pool.buff(pool.count) = v; pool.count += 1 }
  //     // else print("*")
  //     // val size = v.length; val vss = ThreadLocalViewPool.get; vss(size) ::= v
  //     // val len = vss(size).length; if(len%20 == 0) print("{"+len+"}")
  //     // val len = vss(size).length; if(len%1000 == 0) print("{"+len/1000+"K}")
  //   }
  // }  

  // /** Thread-local pools of temporary Views, indexed by size of Views. */
  // private object ThreadLocalTempViewPool extends ThreadLocal[Array[View]]{
  //   override def initialValue() = Array.tabulate(MaxViewSize+1)(new View(_))
  // }

  // /** Get a temporary View of size size.  The use of this View must not overlap
  //   * with the use of any other of the same size obtained in the same way. */
  // def getTempView(size: Int): View = {
  //   val vs = ThreadLocalTempViewPool.get; vs(size)
  // }

  // =================== Useful operations on views

  // /** Insert s into view in place of its ith member (indexing from 0). */
  // def insert(view: View, i: Int, s: State): View = {
  //   // val v1 = view.clone; 
  //   val v1 = newView(view.length); view.copyToArray(v1)
  //   v1(i) = s; v1
  // }

  // /** Insert each state in states into view in place of its ith member (indexing
  //   * from 0). */
  // @inline def insertStates(view: View, i: Int, states: List[State]): List[View]
  //   = states.map(insert(view, i, _))

  // /** Insert each state of states0 into view in position i0, and insert each
  //   * state of states1 in position i1. */
  // @inline def insert2States(view: View, i0: Int, states0: List[State],
  //                           i1: Int, states1: List[State]): List[View] = {
  //   for(s0 <- states0; s1 <- states1) yield{
  //     // val v1 = view.clone; 
  //     val v1 = newView(view.length); view.copyToArray(v1)
  //     v1(i0) = s0; v1(i1) = s1; v1
  //   }
  //   // if(i0 < i1){
  //   //   val (before1, _::after) = view.splitAt(i1)
  //   //   val (before, _::mid) = before1.splitAt(i0)
  //   //   val tails = states1.map(s1 => mid++(s1::after))
  //   //   for(tail <- tails; s0 <- states0) yield before++(s0::tail)
  //   // }
  //   // else insert2States(view, i1, states1, i0, states0)
  // }

  // /** The shape of a view, i.e. an array giving the number of states of each
  //   * process type. */
  // def shape(view: View): Array[Int] = {
  //   val theShape = new Array[Int](numFamilies)
  //   for(st <- view) theShape(st.family) += 1
  //   theShape
  // }

  /** All views of view with shapes from aShapes.
    * @param init is this creating the initial view?  If not, view is assumed
    * to be no larger than an element of cShapes. */
  def alpha(aShapes: List[Array[Int]], view: View, init: Boolean = false) 
      : List[View] = { ??? }
  //   val len = view.length
  //   val lengths = new Array[Int](numFamilies) // Number of States of each type
  //   for(i <- 0 until len){
  //     // assert(view(i).family < numFamilies,
  //     //        show(view)+" "+i+" "+view(i).family+" "+numTypes)
  //     lengths(view(i).family) += 1
  //   }
  //   // assert(init || lengths.forall(_ <= combinations.length)) 
  //   // Restriction of view to each family
  //   val subViews = Array.tabulate(numFamilies)(f => new Array[State](lengths(f)))
  //   val indices = new Array[Int](numFamilies) // indices into above
  //   for(i <- 0 until len){
  //     val st = view(i); val f = st.family
  //     subViews(f)(indices(f)) = st; indices(f) += 1
  //   }
  //   var result = List[View]()
  //   // assert((0 until numFamilies).forall(f => indices(f) == lengths(f)))
  //   // For each family f, all views of the restriction of view to f.
  //   if(init){ // This is necessary for the initial views
  //     val allAlphas: Array[Array[List[View]]] =
  //       Array.tabulate(numFamilies)(f => alpha2(lengths(f), subViews(f)))
  //     for(sh <- aShapes)
  //       // Create all subviews of size sh(f) for each family f, and merge them
  //       // in all possible ways.
  //       if((0 until numFamilies).forall(f => sh(f) <= lengths(f))){
  //         val alphs = Array.tabulate(numFamilies)(f => allAlphas(f)(sh(f)))
  //         result = allMerges(alphs, result)
  //       }
  //     result
  //   }
  //   else{
  //     for(sh <- aShapes)
  //       if((0 until numFamilies).forall(f => sh(f) <= lengths(f))){
  //         val alphs =
  //           Array.tabulate(numFamilies)(f => newAlpha2(sh(f), subViews(f)))
  //         result = allMerges(alphs, result)
  //       }
  //     result
  //   }
  //   // FIXME: recycle intermediate subViews
  // }

  // /** Combinations(n)(r) will contain all subsets of [0..n) of size r, for r <=
  //   * n. */
  // private var combinations: Array[Array[Array[Array[Int]]]] = null

  // /** Initialise combinations.
  //   * @param n1 the maximum value n for which to make combinations(n); the
  //   * maximum number of states of the same type in any concretization. */
  // def makeCombinations(n1: Int) = {
  //   combinations = Array.ofDim[Array[Array[Int]]](n1+1,n1+1)
  //   //combinations(0)(0) = Array(Array[Int]())
  //   for(n <- 0 to n1){
  //     combinations(n)(0) = Array(Array[Int]())
  //     for(r <- 1 until n){
  //       combinations(n)(r) =
  //         combinations(n-1)(r) ++ combinations(n-1)(r-1).map(_ :+ (n-1))
  //       // All subsets of [0..n-1) of size r; and all subsets of [0..n-1) or
  //       // size r-1 with n-1 added.
  //       println(s"($n,$r): "+
  //                 combinations(n)(r).map(_.mkString("<",",",">")).mkString("; "))
  //     }
  //     combinations(n)(n) = Array((0 until n).toArray)
  //   }
  // }

  // /** All views of sv of size k. */
  // private def newAlpha2(k: Int, sv: View) : List[View] = {
  //   val len = sv.length // ; require(k <= len, k+" "+len)
  //   // assert(len < combinations.length, k+" "+show(sv))
  //   val ixss: Array[Array[Int]] = combinations(len)(k)
  //   var result = List[View]()
  //   for(ixs <- ixss) result ::= Array.tabulate(k)(i => sv(ixs(i)))
  //   result
  //   // ixss.map(ixs => Array.tabulate(k)(i => sv(ixs(i))))
  // }


  // /** All views of view of sizes up to k, in an array, indexed by size. */
  // private def alpha2(k: Int, view: View) : Array[List[View]] = {
  //   val views = Array.fill(k+1)(List[View]())
  //   views(0) = List(Array[State]())
  //   // Inv: for all j, views(j) gives all views of size j of
  //   // view[len-i..len); so if i<j then views(i) is empty.
  //   val len = view.length; var i = 0
  //   while(i < len){
  //     i += 1
  //     val s0 = view(len-i)
  //     // for(j <- i to k) assert(views(j).isEmpty)
  //     // Add s0 to each view of size j-1 to create a view of size j
  //     var j = k min i
  //     while(j >= 1){
  //       for(v <- views(j-1)) views(j) ::= s0+:v
  //       j -= 1
  //     }
  //   }
  //   // for(i <- 0 until k+1)  println(i+": "+views(i).map(show))
  //   views
  // }

  // /** All ways of merging one element from each element of subViews, added onto
  //   * accum. */
  // private def allMerges(subViews: Array[List[View]], accum: List[View])
  //     : List[View] = {
  //   var result = accum
  //   if(numFamilies == 1) subViews(0)++result
  //   else{
  //     assert(numFamilies == 2) // FIXME
  //     for(v1 <- subViews(0); v2 <- subViews(1)) result ::= merge(v1, v2)
  //     result
  //   }
  // }

  //  /** Merge views v1 and v2, giving a view with control states in order.  
  //   * 
  //   * Pre: the two views have distinct control states; and each has control
  //   * states in order. */
  // private def merge(v1: View, v2: View): View = {
  //   val len1 = v1.length; val len2 = v2.length
  //   val result = newView(len1+len2)
  //   var i1 = 0; var i2 = 0; var i = 0 // Inv i = i1+i2
  //   while(i1 < len1 && i2 < len2){
  //     val st1 = v1(i1); val st2 = v2(i2)
  //     if(st1.cs < st2.cs){ result(i) = st1; i1 += 1; i += 1 }
  //     else{ assert(st2.cs < st1.cs); result(i) = st2; i2 += 1; i += 1 }
  //   }
  //   while(i1 < len1){ result(i) = v1(i1); i1 += 1; i += 1 }
  //   while(i2 < len2){ result(i) = v2(i2); i2 += 1; i += 1 }
  //   result
  // }

}
