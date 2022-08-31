
/* Run with something like 
 *
 * java --illegal-access=deny -cp
 * .:/usr/share/scala/lib/scala-library.jar:/home/gavin/bin/FDRSym/fdr/lib/fdr.jar:/home/gavin/Scala/Util
 * -javaagent:"/home/gavin/Scala/Util/ox/gavin/profiling/InstrumentationAgent.jar"
 *  -Xmx24g Instrumentation CSP/lockBasedStack.csp --singleRef
 *
 * The classpath must contain the scala standard library, the path for view
 * abstraction, and the path for the gavin.ox.profiling package.  The
 * -javaagent directive should point to the InstrumenationAgent in the
 * gavin.ox.profiling package.  The final arguemtns are the arguments for the
 * view abstraction.  Note the -Xmx argument is necessary, even if JAVA_OPTS
 * is set (or else the standard JVM heap space will be used).  It might also
 * be necessary to use a flag like -Xss200m, to set the stack size (since the
 * memory profiler works recursively).
 */


/** Java class that allows the InstrumentationAgent to be used from Scala. */
public class Instrumentation {
  public static void main(String[] args) {
    ScalaInstrumentation sie = new ScalaInstrumentation();
    sie.apply(args);
  }
}
 
/* 1. Compile with something like 
 *
 * javac -cp .:/users/gavinl/Scala/Util:/users/gavinl/bin/scala/scala-2.12.6/lib/scala-library.jar Instrumentation.java
 *
 * where the classpath includes the location of the standard scala library,
 * and the gavin.ox.profiling package.
 *
 * 2. Run with something like the above
 *
 * where the classpath includes the location of the standard scala library,
 * the FDR jar file, and the gavin.ox.profiling package; and the -javaagent
 * argument points within the gavin.ox.profiling package.
 */
