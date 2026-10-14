package souther.compiler.query;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.SourceOutcome;
import souther.compiler.partition.Replacement;

import java.util.Objects;

/**
 * A rewrite, with what the arms it is about mean in the source.
 *
 * <p>Beside the rewrite and not part of it, as where it is shown is. Which rewrite it is stays the
 * fork and two part numbers, which tell it from every other; what an author is shown is the arm and
 * the arm it answered as, in the words a report writes for an arm. The sibling is often an arm no
 * run through is recorded, so what it means is read off the plan's arms as written and not off its
 * sites.
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
    }

    /** The body answering one value, which is about no arm. */
    record ByOneAnswer(Replacement.ByOneAnswer replacement) implements ReplacementAsWritten {

        public ByOneAnswer {
            Objects.requireNonNull(replacement, "a rewrite is some rewrite");
        }
    }
}
