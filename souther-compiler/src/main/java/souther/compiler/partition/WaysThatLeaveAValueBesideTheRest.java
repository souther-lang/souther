package souther.compiler.partition;

import souther.compiler.inputs.SearchRegion;

import java.util.ArrayList;
import java.util.List;

/**
 * Of the ways a part of a way can be held along, those some way of holding every other part leaves
 * a value beside.
 *
 * <p>A way of holding one part that no way of holding another part leaves a value beside is a way
 * no row is held along, whatever the remaining parts say: a part is all of the conditions it asks,
 * and a row meeting a way meets them with those of the other parts. So what is dropped here is no
 * row, and a part left with none says no row holds the parts together — for as long as the ways it
 * had were every one it could be held along, which is for the caller to ask of the figures.
 *
 * <p>Asked of two parts at a time, which is where conditions on the same numbers meet. A way kept
 * is not shown to be held beside all of them at once, and the composing that follows is what finds
 * a row for the rest.
 */
final class WaysThatLeaveAValueBesideTheRest {

    private WaysThatLeaveAValueBesideTheRest() { }

    /** {@code parts}, each with the ways that leave a value beside some way of every other. */
    static List<List<HeldOutcome>> of(List<List<HeldOutcome>> parts, SearchRegion declarations) {
        List<List<HeldOutcome>> out = new ArrayList<>();
        for (List<HeldOutcome> part : parts) {
            List<HeldOutcome> kept = new ArrayList<>();
            for (HeldOutcome way : part) {
                if (leavesAValue(List.of(way), declarations)
                        && parts.stream().filter(other -> other != part).allMatch(other ->
                                other.stream().anyMatch(with ->
                                        leavesAValue(List.of(way, with), declarations)))) {
                    kept.add(way);
                }
            }
            out.add(kept);
        }
        return out;
    }

    private static boolean leavesAValue(List<HeldOutcome> held, SearchRegion declarations) {
        return HeldOutcome.along(held, declarations) instanceof Reachability.Reaching;
    }
}
