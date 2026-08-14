package souther.compiler.observe;

import java.util.Set;

/**
 * What applied the behavior for one row, and what that application can be measured in.
 *
 * <p>A row's outcome used to record what the row turned out to be and not what produced the answer.
 * With one answerer — the bytecode this compile generated, applied through the loader the run builds
 * — that was invisible, and every number beside it could be read as a fact about the row. It is not:
 * how many counted points an application passed is a question about code this compile emitted the
 * counting into, and there is no answer to it for code this compile did not write.
 *
 * <p>So the numbers live inside the arm they are defined for rather than beside it. A reader holding
 * {@link Generated} has the count and knows what it counts; a reader holding {@link NotRun} has no
 * numbers to misread. Zero and "not measurable here" are different values of different shapes rather
 * than one field a reader has to ask a second question about.
 *
 * <p>What is not here is the arm for an implementation supplied from outside the compile. It has no
 * producer yet — nothing outside a compile applies a behavior today — and an arm nothing writes is a
 * statement about a run that does not happen. It arrives with what writes it (#695), and this being
 * sealed is what makes that arrival a change every reader is held to rather than one they can miss.
 *
 * <p>This says what ran, and nothing else. How a behavior is written is answered where it is written
 * ({@code ExampleVerifier.isPending}), and a second answer to that question is what this must not
 * become. Which arms of a body a row went through is what {@link Generated#hits} says; whose code it
 * was is what the arm says.
 */
public sealed interface Run {

    /**
     * The behavior was not applied.
     *
     * <p>A row whose fixtures did not build, one recorded against a behavior with nothing to run it,
     * one whose dependency had no fake — the reasons differ and {@link Stage} and
     * {@link FailurePhase} are where they are said. What is said here is that no application
     * happened, so there is nothing that applied it and nothing measured about it.
     */
    record NotRun() implements Run {}

    /**
     * The classes this compile generated, applied through the loader this run built.
     *
     * <p>Both numbers are what this compile's own counting read, which is why they are here and not
     * beside the outcome: they are defined for code the emitter counted into and for nothing else.
     *
     * <p>An application that was given up on reads as zero of each, because nothing was read from a
     * worker that is still running — a count taken while it runs is some of what it spent rather than
     * what it spent. Which of the two a zero is remains what the disposition says, as it was before
     * this type: zero counted points is what a body with no loop in it passes.
     *
     * @param steps how many counted points the application passed
     * @param hits  the branch sites it went through; empty until branches are measured
     */
    record Generated(long steps, Set<Integer> hits) implements Run {

        public Generated {
            hits = hits == null ? Set.of() : Set.copyOf(hits);
        }
    }
}
