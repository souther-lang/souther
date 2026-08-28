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
 * arrangement that reached back into the compile for the term it was already told would have two
 * ways to learn one thing, and two ways to learn one thing is how the boundary came to state a
 * minute while the run was given up on after five milliseconds. Asked this way, what the JVM keeps
 * is what the language said it would be held to, because it is the same value — and an arrangement
 * that does not keep it has to take the argument and not use it, where the caller who chose it can
 * see that.
 *
 * <p>The wait and nothing else. What the arrangement itself is made of — a thread, how much stack it
 * is given — belongs to whoever built the arrangement and is settled before this is asked, so the
 * two are not offered here as though a compile said both.
 *
 * <p>This is what a caller replaces to run a compile's rows some other way, and the caller is not
 * only a test: the Java binding runs a row on a worker and hands what the row reaches outside back
 * to the thread that asked. It is named for the machine it is of, and reached through
 * {@code Compilation} — which is where the implementation that uses one is named.
 */
public interface JvmExampleDeadlines {

    /**
     * The arrangement this compile's rows and readings are run under, keeping {@code outerTimeout}.
     *
     * <p>Asked per compile rather than given once, so that the term reaches the arrangement that
     * keeps it rather than being read a second time out of somewhere else.
     */
    Deadline forThisCompile(Duration outerTimeout);
}
