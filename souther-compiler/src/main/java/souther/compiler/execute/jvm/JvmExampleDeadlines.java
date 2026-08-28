package souther.compiler.execute.jvm;

import souther.compiler.examples.Deadline;

/**
 * Where the JVM implementation gets the deadline it runs a row under.
 *
 * <p>Beside {@link JvmProgramImages} and for the same reason. What a run is held to — the steps, the
 * depth, the wait — is the compile's and crosses {@code ProgramExecution} as terms; how those terms
 * are kept is the implementation's, and here it is a worker of this compile's own and a wall clock.
 * A {@link Deadline} is that arrangement, not a term: it takes the work and runs it. So it does not
 * cross the boundary, and the implementation that needs one is handed this instead.
 *
 * <p>Asked per compile rather than given once. What a build uses is built from what the compilation
 * settled; a test says one outright, and says it after the implementation was named. Reading it at
 * the question is what lets the second of those work at all.
 */
public interface JvmExampleDeadlines {

    /** The deadline this compile's rows and readings are run under. */
    Deadline forThisCompile();
}
