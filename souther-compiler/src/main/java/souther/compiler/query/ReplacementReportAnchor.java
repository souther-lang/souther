package souther.compiler.query;

import souther.compiler.coverage.ArmReportAnchor;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.partition.Replacement;
import souther.compiler.types.SourceConstructOrigin;

import java.util.Objects;

/**
 * What a report about a rewrite points at, said without saying where that is.
 *
 * <p>Beside the rewrite and not part of it. A rewrite is a program, and the same arm of the same
 * helper rewritten as the same sibling is one program however many calls in the body reach the
 * helper; where this compilation reached it is one place per call. So a rewrite of an arm is shown
 * where its fork is written when this compilation holds that source, and at the behavior otherwise —
 * one answer for every call, which is what keeps the rewrite one.
 *
 * <p>Settled from the arm's own {@link ArmReportAnchor}, where what the fork is written in can
 * still be seen. Whether a construct was written by some source and whether this compilation holds
 * that source are two questions; the construct alone answers only the first.
 */
public sealed interface ReplacementReportAnchor {

    /** Shown where the fork is written, in a source this compilation holds. */
    record AtTheFork(ArmReportAnchor.WhereItIsWritten fork) implements ReplacementReportAnchor {

        public AtTheFork {
            Objects.requireNonNull(fork, "a rewrite shown at its fork is shown at some fork");
        }
    }

    /** Shown where the walk is written, in a source this compilation holds. */
    record AtTheWalk(SourceConstructOrigin walk) implements ReplacementReportAnchor {

        public AtTheWalk {
            if (walk == null || !walk.isWritten()) {
                throw new IllegalArgumentException("a rewrite shown at its walk is shown at a walk"
                        + " some source wrote: " + walk);
            }
        }
    }

    /** Shown at the behavior whose body it rewrites. */
    record AtTheBehavior() implements ReplacementReportAnchor {}

    /**
     * Whether a rewrite can be shown here: one of the body as a whole stands at no fork and at no
     * walk, and one of an arm or of a walk shown at its fork or walk is shown at its own.
     */
    default boolean shows(Replacement replacement) {
        return switch (this) {
            case AtTheFork(ArmReportAnchor.WhereItIsWritten fork) ->
                    replacement instanceof Replacement.OfAnArm arm
                            && arm.fork().equals(fork.origin());
            case AtTheWalk(SourceConstructOrigin walk) ->
                    replacement instanceof Replacement.OfAWalk rewritten
                            && rewritten.walk().equals(walk);
            case AtTheBehavior _ -> true;
        };
    }

    /** Where a rewrite of the walk at {@code site} is shown. */
    static ReplacementReportAnchor ofAWalk(CoverageSites.WalkSite site) {
        // A place this compilation reached is one per call, and the rewrite is one for all.
        return site.writtenHere() ? new AtTheWalk(site.walk()) : new AtTheBehavior();
    }

    /** Where a rewrite of an arm reported at {@code arm} is shown. */
    static ReplacementReportAnchor ofAnArm(ArmReportAnchor arm) {
        return switch (arm) {
            case ArmReportAnchor.WhereItIsWritten written -> new AtTheFork(written);
            // A place this compilation reached is one per call, and the rewrite is one for all.
            case ArmReportAnchor.WhereItWasReached _ -> new AtTheBehavior();
        };
    }
}
