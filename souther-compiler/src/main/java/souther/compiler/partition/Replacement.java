package souther.compiler.partition;

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
 * <p>What a rewrite is and not what it would answer: the one value a body could be rewritten to
 * answer is whichever value its rows came to, which moves with the rows, and the rewrite asked about
 * does not.
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

    /** The body answering one value whatever it is given. */
    record ByOneAnswer() implements Replacement {}
}
