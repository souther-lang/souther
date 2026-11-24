package souther.compiler.partition;

import souther.compiler.coverage.ArmReplacements;
import souther.compiler.coverage.RunRewrite;
import souther.compiler.coverage.WalkRewrite;
import souther.compiler.coverage.WalkRewrites;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowRef;
import souther.compiler.types.SourceConstructOrigin;

import java.util.Objects;

/**
 * One rewrite of a behavior's body a row could be asked to notice, as the author would make it.
 *
 * <p>Three families and no more. An arm answering as one of its siblings does is the rewrite a fork
 * invites; the body answering one value whatever it is given is the rewrite a body with no fork in it
 * invites, and the one rows that all answer alike cannot tell from it; a walk stopping after its
 * first step, or handing each step the seed, is the rewrite a loop invites, and the one rows of
 * fewer than two elements cannot tell from it.
 *
 * <p>A rewrite is a program, so two rewrites answering two values are two rewrites: a body answering
 * one value is asked once per value the rows came to, and a row that tells one of them apart says
 * nothing about another.
 */
public sealed interface Replacement {

    /**
     * {@code walk} run as {@code how} says: stopping after its first step, or handing every step
     * the seed in the place of what the step before it answered.
     *
     * @param walk the fold the source wrote, in the copy of whatever wrote it
     */
    record OfAWalk(SourceConstructOrigin walk, WalkRewrite how) implements Replacement {

        public OfAWalk {
            Objects.requireNonNull(walk, "a walk is some walk an author wrote");
            Objects.requireNonNull(how, "a walk is rewritten some way");
        }
    }

    /** Which rewrite {@code rewrite} is, as the author would make it. */
    static Replacement of(RunRewrite rewrite) {
        return switch (rewrite) {
            case ArmReplacements.Rewrite arm -> new OfAnArm(arm.fork(), arm.part(), arm.with());
            case WalkRewrites.Rewrite walk -> new OfAWalk(walk.walk(), walk.how());
        };
    }

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
