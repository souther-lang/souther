package souther.compiler.query;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.SourceOutcome;
import souther.compiler.partition.Replacement;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.Objects;

/**
 * A rewrite, with what tells it from the other rewrites of its body in the source.
 *
 * <p>Beside the rewrite and not part of it, as where it is shown is. Which rewrite it is stays the
 * fork and two part numbers, or the value; what an author is shown is what those mean in the
 * source — the arm and the arm it answered as, and the definition that wrote the fork, or the row
 * that came to the value. Held here, once, so that every reader that says
 * a rewrite — the page, a warning, a row composed for it — says it apart from the others by the
 * same facts, and none of them is left to work out its own and drop one.
 *
 * <p>The sibling is often an arm no run through is recorded, so what it means is read off the
 * plan's arms as written and not off its sites.
 */
public sealed interface ReplacementAsWritten {

    /** The rewrite this says. */
    Replacement replacement();

    /**
     * Arm {@code replacement.part()} answering as arm {@code replacement.with()} does.
     *
     * @param arm     what the arm rewritten means
     * @param sibling what the arm it answers as means
     */
    record OfAnArm(Replacement.OfAnArm replacement, SourceOutcome.Arm arm,
                   SourceOutcome.Arm sibling) implements ReplacementAsWritten {

        public OfAnArm {
            Objects.requireNonNull(replacement, "a rewrite is some rewrite");
            Objects.requireNonNull(arm, "the arm rewritten means something");
            Objects.requireNonNull(sibling, "and so does the arm it answers as");
        }

        /** {@code replacement} as {@code plan}'s walk met its two arms. */
        public static OfAnArm in(CoverageSites.Plan plan, Replacement.OfAnArm replacement) {
            return new OfAnArm(replacement,
                    plan.outcomeOf(new CoverageSites.AsWritten(replacement.fork(),
                            replacement.part())),
                    plan.outcomeOf(new CoverageSites.AsWritten(replacement.fork(),
                            replacement.with())));
        }

        /**
         * The definition that wrote the fork, which is what tells two forks apart where this
         * build holds no source of either to point at.
         *
         * <p>The definition and not the name a call reached it by. A rewrite is one for every call
         * that reaches the fork, and each call may spell its way in differently; which definition
         * wrote the fork is one answer for all of them.
         */
        public ValueName.Helper writtenBy() {
            WrittenOwner.Body body = WrittenOwner.theBodyThatWrote(replacement.fork().owner());
            return new ValueName.Helper(body.module(), body.definition());
        }
    }

    /**
     * The body answering one value, told from another value's by the row that came to it
     * ({@link Replacement.ByOneAnswer#answeredBy}).
     *
     * <p>The row and not where it is written. A finding holds what it is about, and a reader that
     * sends somebody to the row asks where it is when it does; a place held here would be the
     * finding carrying where a row stood when it was made.
     */
    record ByOneAnswer(Replacement.ByOneAnswer replacement) implements ReplacementAsWritten {

        public ByOneAnswer {
            Objects.requireNonNull(replacement, "a rewrite is some rewrite");
        }
    }
}
