package souther.compiler.partition;

import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowRef;
import souther.compiler.types.SourceConstructOrigin;

import java.util.Objects;

/**
 * One rewrite of a behavior's body a row could be asked to notice, as the author would make it.
 *
 * <p>Two families and no more. An arm answering as one of its siblings does is the rewrite a fork
 * invites; the body answering one value whatever it is given is the rewrite a body with no fork in it
 * invites, and the one rows that all answer alike cannot tell from it. Which rewrites are asked about
 * is fixed here and not read off how the body happens to be lowered, so a change in the library
 * under a body is not a change in what its rows are held to.
 *
 * <p>A rewrite is a program, so two rewrites answering two values are two rewrites: a body answering
 * one value is asked once per value the rows came to, and a row that tells one of them apart says
 * nothing about another.
 */
public sealed interface Replacement {

    /** Arm {@code part} of {@code fork} answering as its sibling {@code with} does. */
    record OfAnArm(SourceConstructOrigin fork, int part, int with) implements Replacement {

        public OfAnArm {
            Objects.requireNonNull(fork, "an arm is an arm of some fork");
            if (part == with) {
                throw new IllegalArgumentException("an arm answering as itself is the arm: part "
                        + part + " of " + fork);
            }
        }
    }

    /**
     * The body answering {@code answer} whatever it is given.
     *
     * @param answer     the value, read in full everywhere inside it
     * @param answeredBy the first row that answered it, which is how a reader outside this compiler
     *                   is sent to the value: a row is named in the module's own words, and a value
     *                   would have to be written out in a form of its own
     */
    record ByOneAnswer(ObservedValue answer, RowRef answeredBy) implements Replacement {

        public ByOneAnswer {
            Objects.requireNonNull(answer, "a body answering one value answers some value");
            Objects.requireNonNull(answeredBy, "and some row answered it");
            if (!Limits.UNBOUNDED.admits(answer)) {
                throw new IllegalArgumentException("a body answering one value answers a value read"
                        + " in full, everywhere inside it: " + answer);
            }
        }
    }
}
