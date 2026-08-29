package souther.compiler.coverage;

import souther.compiler.types.BinOp;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Optional;

/**
 * What one way through a coverage construct means, said in the source's own terms.
 *
 * <p>Half of an answer. Which construct this is an outcome of is {@link CoverageSites.Site}'s other
 * half, read off the {@link souther.compiler.types.CoverageOrigin} its obligation carries, and the
 * meaning is the two together: a condition holding is {@code then} under an {@code if}, the rest of
 * the block under a {@code guard}, and an element kept under a comprehension. The construct is not
 * repeated here, so nothing can say one construct in one component and another in the next.
 *
 * <p>Data and not words. What a report calls an outcome is a rendering, chosen where a reader is and
 * in the language they asked for; deciding it while the tree is being walked freezes one language's
 * word into the analysis, which is how {@code then} came to be printed for constructs that have no
 * {@code then} in them.
 */
public sealed interface SourceOutcome {

    /**
     * The way taken because the decision held.
     *
     * <p>Not always an arm the author wrote. A {@code guard}'s is the rest of the block and a
     * comprehension's is the element it yields, and what says which of those this is, is the
     * construct beside it.
     */
    record Held(HeldBy by) implements SourceOutcome {}

    /** The way taken because the decision did not hold. */
    record Failed(FailedBy by) implements SourceOutcome {}

    /**
     * What held.
     *
     * <p>Beside the construct rather than inside it, because the two vary on their own: an
     * {@code if} and a {@code guard} each come in both shapes, and a comprehension only ever
     * decides on a condition.
     */
    sealed interface HeldBy {

        /** A condition came out true. */
        record Condition() implements HeldBy {}

        /** A value was built, so its invariant is what held. Nothing to name: a construction that
         *  succeeded broke no clause. */
        record Construction() implements HeldBy {}
    }

    /** What did not hold, which has one thing to say that {@link HeldBy} does not. */
    sealed interface FailedBy {

        /** A condition came out false. */
        record Condition() implements FailedBy {}

        /**
         * A value was refused by its invariant.
         *
         * @param clause which clause this departure answers, where the source named one, and empty
         *               where it takes any failure
         */
        record Construction(Optional<String> clause) implements FailedBy {

            public Construction {
                clause = clause == null ? Optional.empty() : clause;
            }
        }
    }

    /**
     * One arm of a {@code match}.
     *
     * @param cases the cases written on the arm. Several where the source wrote them together, which
     *              is one run of code and so one arm
     */
    record Matched(List<TypeSymbol> cases) implements SourceOutcome {

        public Matched {
            cases = List.copyOf(cases);
        }
    }

    /**
     * One comparison of a condition, recorded where it produced its answer.
     *
     * <p>Not an arm and counted as one nowhere. A condition stops as soon as it is settled, so which
     * arm a row landed in does not say which comparison ran.
     */
    record Compared(BinOp op) implements SourceOutcome {}

    /** Whether this is one of the arms a branch measure counts. */
    default boolean isArm() {
        return switch (this) {
            case Compared _ -> false;
            case Held _, Failed _, Matched _ -> true;
        };
    }
}
