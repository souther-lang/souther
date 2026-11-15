package souther.compiler.reading;

import souther.compiler.core.Core;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;

import java.util.ArrayList;
import java.util.List;

/**
 * The ways a comparison of how many elements something keeps comes out, as the decisions that keep
 * them.
 *
 * <p>{@code List.length(List.filter(p, [a, b])) >= 1} comes out true where {@code a} is kept, where
 * {@code b} is, or where both are, and false where neither is. Each element's keeping is a decision
 * {@link KeptElements} already reads; the comparison is a statement about how many of them hold, and
 * its ways are the assignments of the decisions that make it come out as asked. A way is every
 * decision decided one way or the other, so the ways are apart: a row is in one of them and no
 * other.
 *
 * <p>Nothing here reads what {@code filter} means. A comparison of a count against a number the
 * body writes is the only shape asked; anything else has no ways written down, which is no claim
 * that it has none.
 */
final class WaysOfACount {

    /** How many elements the assignments are worked through for. The ways are as many as two to
     *  this, which is {@link CoverageNaming#MOST_OUTCOMES}. */
    private static final int MOST_ELEMENTS = 6;

    private WaysOfACount() {}

    /**
     * The ways {@code condition} comes out {@code want}, or null where it is not a comparison of a
     * count with a number or its decisions were not read.
     *
     * @param body the body {@code condition} is in, which is where a list named by a {@code let} is
     *             found
     */
    static List<WayIn> of(Core condition, boolean want, KeptElements kept, CoverageNaming naming,
                          Core body) {
        if (!(Core.withoutStanding(condition) instanceof Core.Binary comparison)
                || !comparison.op().compares()) {
            return null;
        }
        Core.Call call;
        long than;
        Rel relation = relationOf(comparison.op());
        if (Core.withoutStanding(comparison.left()) instanceof Core.Call counted
                && Core.withoutStanding(comparison.right()) instanceof Core.Int number) {
            call = counted;
            than = number.value();
        } else if (Core.withoutStanding(comparison.right()) instanceof Core.Call counted
                && Core.withoutStanding(comparison.left()) instanceof Core.Int number) {
            call = counted;
            than = number.value();
            relation = relation.turned();
        } else {
            return null;
        }
        if (!Meetings.consumesItsElements(call) || Meetings.combinesItsElements(call)) {
            return null;
        }
        if (!(kept.of(call, naming, body, true) instanceof KeptElements.Read.Factors(var each))
                || each.isEmpty() || each.size() > MOST_ELEMENTS) {
            return null;
        }
        List<WayIn> ways = new ArrayList<>();
        for (int assignment = 0; assignment < 1 << each.size(); assignment++) {
            if (relation.holds(Long.compare(Integer.bitCount(assignment), than)) != want) {
                continue;
            }
            List<Decision> way = new ArrayList<>();
            for (int element = 0; element < each.size() && way != null; element++) {
                List<Outcome> sides = each.get(element).outcomes();
                boolean kept1 = (assignment >> element & 1) == 1;
                way = CoverageNaming.merge(way, sides.get(kept1 ? 0 : 1).holds());
            }
            if (way != null) {
                ways.add(new WayIn(way));
            }
        }
        return ways.isEmpty() ? null : ways;
    }

    /** The relation a comparison operator writes, read with its left side first. */
    private static Rel relationOf(BinOp op) {
        return switch (op) {
            case EQ -> Rel.EQ;
            case NE -> Rel.NE;
            case LT -> Rel.LT;
            case LE -> Rel.LE;
            case GT -> Rel.GT;
            case GE -> Rel.GE;
            default -> throw new IllegalArgumentException(op + " is no comparison");
        };
    }
}
