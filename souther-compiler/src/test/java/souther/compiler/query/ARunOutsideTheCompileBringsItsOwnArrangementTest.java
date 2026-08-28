package souther.compiler.query;

import souther.compiler.WhatWasCompiled;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The arrangement a compile runs its own rows under is the compile's, and is not taken over.
 *
 * <p>What every run of one model's rows has to agree on is the program and the terms. Two runs
 * against different classes are not two runs of one model, and two runs under different limits do
 * not say one thing about it — which is why {@code Compilation} holds one
 * {@code JvmProgramImages} and one {@code EvaluationPolicy}. How a run keeps those terms is not on
 * that list, and reading it as though it were is what this holds against: an arrangement was written
 * for a run that reaches an implementation in the caller's world, and giving the compile's own
 * evaluation the same one handed it a way of running rows that was made for somewhere else. What
 * followed was that the compile stopped keeping the wait it states, since that arrangement is the
 * one that cannot keep it.
 *
 * <p>So a caller that runs rows of its own builds the arrangement its world needs and hands it to
 * that run. It does not reach into the compilation and replace what the compile decides with.
 *
 * <p>What may is the compiler's own entry points, which name an arrangement for a caller that asked
 * for one — a test stating that a row does not come back. That is the seam
 * {@link Compilation#withJvmExampleDeadlines} is, and it is the JVM execution's rather than every
 * run's.
 */
class ARunOutsideTheCompileBringsItsOwnArrangementTest {

    /**
     * Nothing but the compiler's entry points takes over what a compile runs its rows under.
     *
     * <p>Read from the calls that were compiled rather than from what a file says, so a call written
     * inside a lambda or behind a helper counts the same as one written outright.
     */
    @Test
    void nothingOutsideTheCompilerReplacesWhatTheCompileRunsItsRowsUnder() {
        Set<String> callers = WhatWasCompiled.callersOf(
                Compilation.class, "withJvmExampleDeadlines");

        assertEquals(Set.of("souther.compiler.Compiler"), callers,
                "the arrangement a compile decides its rows under is the compile's; a caller"
                        + " running rows in a world of its own hands that run its own arrangement"
                        + " rather than replacing this one");
    }
}
