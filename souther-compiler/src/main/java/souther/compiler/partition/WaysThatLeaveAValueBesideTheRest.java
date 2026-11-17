package souther.compiler.partition;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Of the ways each part of a way can be held along, those some way of holding every other part
 * leaves a value beside.
 *
 * <p>A way of holding one part that no way of holding another part leaves a value beside is a way
 * no row is held along, whatever the remaining parts say: a part is all of the conditions it asks,
 * and a row meeting a way meets them with those of the other parts. So what is dropped here is no
 * row. Asked of two parts at a time, which is where conditions on the same numbers meet; a way
 * that stays is not shown to be held beside all of them at once, and the composing that follows is
 * what finds a row for the rest.
 *
 * <p>A part left with none says no row holds the parts together, but only where every way the part
 * had was one that was looked at. Where a figure left ways of some part out, the ones that went
 * may be the ones another part's ways were held beside, so what is said is the figure and not a
 * proof.
 */
final class WaysThatLeaveAValueBesideTheRest {

    private WaysThatLeaveAValueBesideTheRest() { }

    /** What the parts come to. */
    sealed interface Beside {

        /** Each part with the ways that stay, which every part still has one of. */
        record Remaining(List<List<HeldOutcome>> parts) implements Beside {

            public Remaining {
                parts = parts.stream().map(List::copyOf).toList();
            }
        }

        /** Some part has none left and every way of it was looked at: no row holds the parts
         *  together. */
        record NoneHolds() implements Beside {}

        /** Some part has none left, and {@code figures} left ways of some part unlooked at. */
        record NotEveryWayWasLookedAt(Set<CompositionBudget> figures) implements Beside {}
    }

    /**
     * {@code parts} put to each other.
     *
     * @param cutShort       the figures that left ways of some part out, none where none did
     * @param leavesAValue   whether the ways it is given, one or two of them, leave a value
     *                       together
     */
    static Beside of(List<List<HeldOutcome>> parts, Set<CompositionBudget> cutShort,
                     Predicate<List<HeldOutcome>> leavesAValue) {
        List<List<HeldOutcome>> out = new ArrayList<>();
        for (int at = 0; at < parts.size(); at++) {
            List<HeldOutcome> kept = new ArrayList<>();
            for (HeldOutcome way : parts.get(at)) {
                if (leavesAValue.test(List.of(way))
                        && besideSomeWayOfEveryOther(way, at, parts, leavesAValue)) {
                    kept.add(way);
                }
            }
            out.add(kept);
        }
        if (out.stream().noneMatch(List::isEmpty)) {
            return new Beside.Remaining(out);
        }
        return cutShort.isEmpty() ? new Beside.NoneHolds()
                : new Beside.NotEveryWayWasLookedAt(cutShort);
    }

    private static boolean besideSomeWayOfEveryOther(HeldOutcome way, int at,
                                                     List<List<HeldOutcome>> parts,
                                                     Predicate<List<HeldOutcome>> leavesAValue) {
        for (int other = 0; other < parts.size(); other++) {
            if (other != at && parts.get(other).stream()
                    .noneMatch(with -> leavesAValue.test(List.of(way, with)))) {
                return false;
            }
        }
        return true;
    }
}
