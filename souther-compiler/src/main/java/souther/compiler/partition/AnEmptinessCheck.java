package souther.compiler.partition;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.types.ValueName;

/**
 * Whether a comparison is a size held against a number that parts nought from every size above it
 * — which is asking whether the container holds anything, however it is spelt.
 *
 * <p>Which comparisons do is worked out from the relation, not listed. {@code == 0} and
 * {@code /= 0} are the check by the library's own word and need nothing else. An ordering needs
 * where the library says a size starts: a size is a count no lower than nought, so {@code <= 0}
 * and {@code < 1} hold exactly where the container is empty, and {@code > 0} and {@code >= 1}
 * exactly where it is not. A size held against a number that parts sizes above nought —
 * {@code >= 2}, {@code == 1} — counts what the container holds and is the comparison it is.
 *
 * <p>The spelling is spent before this is asked. {@code List.isEmpty(ys)} and
 * {@code List.length(ys) == 0} reach here as the one statement ({@link
 * souther.compiler.check.BooleanMeaning#asAComparison}).
 */
final class AnEmptinessCheck {

    private AnEmptinessCheck() {}

    /**
     * What a comparison says of whether a container holds anything.
     *
     * @param container         the container whose size is held against nought
     * @param emptyWhereItHolds whether the comparison holding is the container holding nothing
     */
    record Checked(Core container, boolean emptyWhereItHolds) {}

    /**
     * The emptiness {@code stated} checks, or null where it is no size held against a number that
     * parts nought from every size above it.
     */
    static Checked checked(StatedComparison stated) {
        StatedComparison.Numbered<AnOperationApplied> size = stated.at(AnEmptinessCheck::aSize);
        if (size == null
                || !(Core.withoutStanding(size.other()) instanceof Core.Int against)) {
            return null;
        }
        Rel relation = size.claim().statedRelation();
        boolean atNought = relation.holds(Long.compare(0, against.value()));
        boolean above = relation.holds(1);
        if (atNought == above) {
            return null;
        }
        // Held equal or unequal to nought, the comparison is the check the library says it means,
        // whatever else is known of the size: it comes out one way at nought and the other way on
        // either side of it.
        boolean noughtAlone = against.value() == 0 && relation.holds(-1) == above;
        return noughtAlone || partsNoughtFromEverySizeAbove(relation, against.value(),
                        size.number().operation())
                ? new Checked(size.number().args().getFirst(), atNought) : null;
    }

    /**
     * Whether {@code relation} against {@code against} comes out the same at every size above
     * nought, where {@code operation} answers no size below it.
     *
     * <p>Only there does an ordering part nought from the rest: {@code >= 1} is {@code /= 0} for
     * a count and for nothing that can be negative. Above nought a size is one or more. Far enough
     * above, every size is above what it is held against; nearer, it may stand at it or below it,
     * and the comparison has to come out the same there too.
     */
    private static boolean partsNoughtFromEverySizeAbove(Rel relation, long against,
                                                        ValueName operation) {
        boolean above = relation.holds(1);
        return (against < 1 || relation.holds(0) == above)
                && (against < 2 || relation.holds(-1) == above)
                && startsAtNought(operation);
    }

    /**
     * Whether the least a size {@code operation} answers is nought, as the library bounds its
     * result — the one value an emptiness check is the size standing at.
     */
    private static boolean startsAtNought(ValueName operation) {
        Endpoint least = ResultRange.of(DefaultBoundOperationFacts.get().boundsOnTheResult(operation),
                ConstantArguments.none()).min();
        return least != null && least.inclusive() && least.at().compareTo(Count.ZERO) == 0;
    }

    /**
     * {@code e} as the size of the one container it is handed, or null where it is no size an
     * emptiness check is read as.
     *
     * <p>Which operations those are is the library's: the sizes its emptiness checks mean, and no
     * others.
     */
    private static AnOperationApplied aSize(Core e) {
        AnOperationApplied applied = AnOperationApplied.of(e);
        if (applied == null || applied.args().size() != 1) {
            return null;
        }
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        for (ValueName check : facts.meansTheSameAsASizeOfNought()) {
            if (facts.meansTheSameAsASizeOfNought(check).size().operation()
                    .equals(applied.operation())) {
                return applied;
            }
        }
        return null;
    }
}
