package souther.compiler.reach;

import souther.compiler.diag.SourcePos;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.types.OccurrenceLineage;

/**
 * One fork on the way to a place, and the way it went.
 *
 * <p>Collected where the assumption is made and not worked out afterwards from where the place
 * sits. A reading that rebuilt this from the tree would be a second account of what was assumed,
 * and the one that matters is the one the domains were actually given — a condition of a shape
 * nothing could take in is not on this list, and a proof naming it would be claiming it did work
 * it did not do.
 *
 * <p>Which copy it was taken in is part of it. A place inside a helper's body is evaluated once
 * for every call the helper is copied into, and a proof is a claim about evaluations: two
 * decisions at one place in two copies are two decisions, and only the lineage tells them apart.
 *
 * @param at      where the condition or the arm is written
 * @param lineage which copy of the body that wrote it the fork or the operator is in
 * @param way     which way the fork went on the way here
 */
public record PathDecision(SourcePos at, OccurrenceLineage lineage, Way way) {

    /** Which way a fork went. */
    public enum Way {
        /** A condition, held. */
        HELD,
        /** A condition, failed. */
        FAILED,
        /** An arm of a {@code match}, taken: the value is one of the cases it selects. */
        TAKEN,
        /** An operator, answered: what it was worked out of lies where it answers a value
         *  ({@link WhereAnOperatorAnswers}). */
        ANSWERED
    }

    public PathDecision {
        if (at == null) {
            throw new IllegalArgumentException("a fork written nowhere decided nothing");
        }
        if (lineage == null) {
            throw new IllegalArgumentException("a fork is in some copy of the body that wrote it: "
                    + at);
        }
        if (way == null) {
            throw new IllegalArgumentException("a fork went some way");
        }
    }

    /**
     * Which of the four a reader says for this fork, chosen by the way it went.
     *
     * <p>Chosen here, so that a reader saying it holds no table of the ways and a way added later
     * stops this compiling rather than any of them.
     */
    public <T> T said(T held, T failed, T taken, T answered) {
        return switch (way) {
            case HELD -> held;
            case FAILED -> failed;
            case TAKEN -> taken;
            case ANSWERED -> answered;
        };
    }

    /** A condition at {@code at}, held where {@code held} says so and failed otherwise. */
    public static PathDecision ofACondition(SourcePos at, OccurrenceLineage lineage,
                                            boolean held) {
        return new PathDecision(at, lineage, held ? Way.HELD : Way.FAILED);
    }

    /** An arm at {@code at}, taken. */
    public static PathDecision ofAnArm(SourcePos at, OccurrenceLineage lineage) {
        return new PathDecision(at, lineage, Way.TAKEN);
    }

    /** An operator at {@code at}, which a run got past only where it answered. */
    public static PathDecision ofAnAnswer(SourcePos at, OccurrenceLineage lineage) {
        return new PathDecision(at, lineage, Way.ANSWERED);
    }
}
