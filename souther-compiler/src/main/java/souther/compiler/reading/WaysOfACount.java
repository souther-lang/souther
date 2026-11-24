package souther.compiler.reading;

import souther.compiler.core.Core;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;

/**
 * The ways a comparison of how many elements something keeps comes out, as the decisions that keep
 * them.
 *
 * <p>{@code List.length(List.filter(p, [a, b])) >= 1} comes out true where {@code a} is kept, where
 * {@code b} is, or where both are, and false where neither is. Each element's keeping is a decision
 * {@link KeptElements} already reads; the comparison is a statement about how many elements are
 * kept, which is those kept whatever a row chooses and the weight of each decision that keeps, and
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
        Rel relation = comparison.op().relation();
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
        // Only where how many are kept whatever a row chooses is known: the ways are the
        // assignments of the decisions that bring the count out as asked, and a count that rests on
        // an element nobody worked out is one they would get wrong.
        if (!(kept.of(call, naming, body, true) instanceof KeptElements.Read.Factors found)
                || found.fixed().isEmpty() || found.each().isEmpty()
                || found.each().size() > MOST_ELEMENTS) {
            return null;
        }
        List<Factor> each = found.each();
        List<WayIn> ways = new ArrayList<>();
        for (int assignment = 0; assignment < 1 << each.size(); assignment++) {
            long count = found.fixed().getAsInt();
            for (int element = 0; element < each.size(); element++) {
                if ((assignment >> element & 1) == 1) {
                    count += found.weights().get(element);
                }
            }
            if (relation.holds(Long.compare(count, than)) != want) {
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

}
