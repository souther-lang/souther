package souther.compiler.execute.jvm;

import souther.compiler.examples.Deadline;

import java.time.Duration;

/**
 * Where the JVM implementation gets the deadline it runs a row under.
 *
 * <p>Beside {@link JvmProgramImages} and for the same reason. What a run is held to — the steps, the
 * depth, the wait — is the compile's and crosses {@code ProgramExecution} as terms; how those terms
 * are kept is the implementation's, and here it is a worker of this compile's own and a wall clock.
 * A {@link Deadline} is that arrangement, not a term: it takes the work and runs it. So it does not
 * cross the boundary, and the implementation that needs one is handed this instead.
 *
 * <p>The wait is passed in rather than fetched, and that is the whole point of the signature. An
 * implementation that reached back into the compile for the term it was already told would have two
 * ways to learn one thing, and two ways to learn one thing is how the boundary came to state a
 * minute while the run was given up on after five milliseconds. Asked this way, what the JVM keeps
 * is what the language said it would be held to, because it is the same value.
 *
 * <p>Asked per compile rather than given once. What a build uses is built from the term; a test says
 * the arrangement outright, and says it after the implementation was named. Reading that at the
 * question is what lets the second of those work at all.
 */
public interface JvmExampleDeadlines {

    /**
     * The arrangement this compile's rows and readings are run under, keeping {@code outerTimeout}.
     *
     * <p>An arrangement a caller said outright answers for the wait itself and this is then what it
     * already decided, which is what saying one outright is for.
     */
    Deadline forThisCompile(Duration outerTimeout);
}
