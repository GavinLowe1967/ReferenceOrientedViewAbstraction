
/* Run with
 * java --illegal-access=deny -cp .:/home/gavin/bin/scala-2.13.1/lib/scala-library.jar:/home/gavin/Scala/Util:/home/gavin/bin/FDRSym/fdr/lib/fdr.jar -javaagent:"/home/gavin/Scala/Util/ox/gavin/profiling/InstrumentationAgent.jar" -Xmx320g Instrumentation
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
 * 2. Run with something like 
 * 
 * java -cp .:/users/gavinl/bin/scala/scala-2.12.6/lib/scala-library.jar:/users/gavinl/bin/FDR4/fdr/lib/fdr.jar:/users/gavinl/Scala/Util -javaagent:"/users/gavinl/Scala/Util/ox/gavin/profiling/InstrumentationAgent.jar" -Xmx24g Instrumentation CSP/lockBasedStack.csp
 *
 * where the classpath includes the location of the standard scala library,
 * the FDR jar file, and the gavin.ox.profiling package; and the -javaagent
 * argument points within the gavin.ox.profiling package.
 */
