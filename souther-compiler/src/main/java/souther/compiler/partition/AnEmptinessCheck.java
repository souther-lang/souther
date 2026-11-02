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
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

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
     * What a comparison says of whether containers hold anything.
     *
     * @param containers        the containers whose sizes are added up and held against nought,
     *                          one where a size alone is
     * @param emptyWhereItHolds whether the comparison holding is the containers holding nothing
     */
    record Checked(List<Core> containers, boolean emptyWhereItHolds) {

        Checked {
            containers = List.copyOf(containers);
        }
    }

    /**
     * The emptiness {@code stated} checks of one container, or null where it is no size held
     * against a number that parts nought from every size above it.
     */
    static Checked checked(StatedComparison stated) {
        Checked all = checkedSizes(stated);
        return all != null && all.containers().size() == 1 ? all : null;
    }

    /**
     * The emptiness {@code stated} checks of several containers, where it is their sizes added up
     * and held against a number that parts nought from every sum above it — or null where it is
     * no such sum.
     *
     * <p>A size is no lower than nought, so a sum of them is nought exactly where every one is and
     * is one or more exactly where some one is: the comparison holds exactly where some container
     * holds something, or exactly where none does. Any other way of combining sizes — taking one
     * from another, weighing one more than the rest — is a relation between them, and is not
     * this.
     */
    static Checked checkedSum(StatedComparison stated) {
        Checked all = checkedSizes(stated);
        return all != null && all.containers().size() > 1 ? all : null;
    }

    private static Checked checkedSizes(StatedComparison stated) {
        StatedComparison.Numbered<List<AnOperationApplied>> sizes =
                stated.at(AnEmptinessCheck::sizesAdded);
        if (sizes == null
                || !(Core.withoutStanding(sizes.other()) instanceof Core.Int against)) {
            return null;
        }
        Rel relation = sizes.claim().statedRelation();
        boolean atNought = relation.holds(Long.compare(0, against.value()));
        boolean above = relation.holds(1);
        if (atNought == above) {
            return null;
        }
        // Held equal or unequal to nought, the comparison is the check the library says it means,
        // whatever else is known of the size: it comes out one way at nought and the other way on
        // either side of it.
        boolean noughtAlone = against.value() == 0 && relation.holds(-1) == above;
        if (!noughtAlone && !sizes.number().stream().allMatch(size ->
                partsNoughtFromEverySizeAbove(relation, against.value(), size.operation()))) {
            return null;
        }
        return new Checked(sizes.number().stream().map(size -> size.args().getFirst()).toList(),
                atNought);
    }

    /**
     * The sizes {@code e} adds up, or null where it is not sizes and nothing else added together.
     */
    private static List<AnOperationApplied> sizesAdded(Core e) {
        if (Core.withoutStanding(e) instanceof Core.Binary sum && sum.op() == BinOp.ADD) {
            List<AnOperationApplied> left = sizesAdded(sum.left());
            List<AnOperationApplied> right = left == null ? null : sizesAdded(sum.right());
            if (right == null) {
                return null;
            }
            List<AnOperationApplied> both = new ArrayList<>(left);
            both.addAll(right);
            return both;
        }
        AnOperationApplied size = aSize(e);
        return size == null ? null : List.of(size);
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
