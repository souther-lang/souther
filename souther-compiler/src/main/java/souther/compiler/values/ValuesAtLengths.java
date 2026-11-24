package souther.compiler.values;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * Values of some sets, each at some lengths: a union of the regions {@link ValuesWithin} is one of.
 *
 * <p>A side of a rule and a class of a position, as {@link ValuesWithin} is a region left open.
 * The strings no longer than a partner can be are one region; the strings shorter than its fewest
 * code points or longer than its most are two, which are one side and one class all the same; and
 * the strings a conversion may stop on are the strings of a language at the lengths past what it is
 * gotten past at every string, with the rest of the side at those lengths a region of its own. The
 * lengths are held as numbers beside the set, because a run of lengths made into one set of strings
 * is a machine as long as the run, and a long one is past what this compiler builds.
 *
 * <p>Kept apart, in order of their fewest code points, and as few as there are: regions of one
 * set at lengths that touch are one region, so two of these holding the same values are equal
 * whichever way they were put together. A region holding no value is none. A value that is no
 * string has no length: where the lengths are every length it is whatever the set holds, and where
 * they are not it is none of these.
 *
 * @param pieces the regions
 */
public record ValuesAtLengths(List<ValuesWithin> pieces) {

    public ValuesAtLengths {
        if (pieces == null) {
            throw new IllegalArgumentException("a region of values, and lengths a value of it may have");
        }
        List<ValuesWithin> sorted = new ArrayList<>(pieces.stream()
                .filter(each -> !each.values().isEmpty()).toList());
        sorted.sort(Comparator.comparingLong(ValuesWithin::shortest));
        List<ValuesWithin> joined = new ArrayList<>();
        for (ValuesWithin each : sorted) {
            boolean merged = false;
            for (int at = joined.size() - 1; at >= 0 && !merged; at--) {
                ValuesWithin last = joined.get(at);
                if (last.values().equals(each.values())
                        && (last.longest() == null || last.longest() + 1 >= each.shortest())) {
                    Long most = last.longest() == null || each.longest() == null ? null
                            : Long.valueOf(Math.max(last.longest(), each.longest()));
                    joined.set(at, new ValuesWithin(last.values(), last.shortest(), most));
                    merged = true;
                }
            }
            if (!merged) {
                joined.add(each);
            }
        }
        pieces = List.copyOf(joined);
    }

    /** Every value of {@code values}, whatever its length. */
    public static ValuesAtLengths all(ValueSet values) {
        return new ValuesAtLengths(List.of(ValuesWithin.all(values)));
    }

    /** The values {@code within} holds, at the one run of lengths it holds them to. */
    public static ValuesAtLengths of(ValuesWithin within) {
        return new ValuesAtLengths(List.of(within));
    }

    /** The values of {@code values} at any of the runs {@code each} holds its own to. */
    public static ValuesAtLengths atAnyOf(ValueSet values, List<ValuesWithin> each) {
        return new ValuesAtLengths(each.stream().map(run -> run.over(values)).toList());
    }

    /** Whether a length bounds any of these beside its set. */
    public boolean bounded() {
        return pieces.stream().anyMatch(ValuesWithin::bounded);
    }

    /** Whether {@code value} is one of these. */
    public boolean has(Value value) {
        return pieces.stream().anyMatch(each -> each.has(value));
    }

    /** Whether one of these is shown to be a value: one of some region is
     *  ({@link ValuesWithin#shownToHoldAValue}). */
    public boolean shownToHoldAValue() {
        return pieces.stream().anyMatch(ValuesWithin::shownToHoldAValue);
    }

    /** Whether none of these is shown to be one: none of any region is. */
    public boolean shownToHoldNone() {
        return pieces.stream().allMatch(ValuesWithin::shownToHoldNone);
    }
}
