package souther.compiler.values;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * The values of a set whose length is in one of some runs of lengths.
 *
 * <p>A side of a rule and a class of a position, as {@link ValuesWithin} is a region left open:
 * the strings no longer than a partner can be are one run, and the strings shorter than its
 * fewest code points or longer than its most are two, which are one side and one class all the
 * same. Held as numbers beside the set, because a run of lengths made into one set of strings is a
 * machine as long as the run, and a long one is past what this compiler builds.
 *
 * <p>The runs are kept apart, in order, and two that touch are one, so one set of values is one
 * value of this. A value that is no string has no length: where the runs are every length it is
 * whatever the set holds, and where they are not it is none of these.
 *
 * @param values the set
 * @param runs   the lengths, each run from its fewest code points to its most; none where no
 *               value is of any
 */
public record ValuesAtLengths(ValueSet values, List<Run> runs) {

    /**
     * Every length from {@code shortest} to {@code longest} code points.
     *
     * @param shortest the fewest
     * @param longest  the most, or null where only the set bounds them
     */
    public record Run(long shortest, Long longest) {

        public Run {
            if (shortest < 0 || (longest != null && longest < shortest)) {
                throw new IllegalArgumentException("a run of lengths a string may have");
            }
        }

        /** The run {@code values} is held to. */
        public static Run of(ValuesWithin values) {
            return new Run(values.shortest(), values.longest());
        }

        /** The lengths of both runs, or null where they share none. */
        Run and(Run other) {
            long fewest = Math.max(shortest, other.shortest);
            Long most = longest == null ? other.longest
                    : other.longest == null ? longest
                    : Long.valueOf(Math.min(longest, other.longest));
            return most != null && most < fewest ? null : new Run(fewest, most);
        }
    }

    /** Every length a string has. */
    private static final Run EVERY = new Run(0, null);

    public ValuesAtLengths {
        if (values == null || runs == null) {
            throw new IllegalArgumentException("a set, and lengths a value of it may have");
        }
        List<Run> sorted = new ArrayList<>(runs);
        sorted.sort(Comparator.comparingLong(Run::shortest));
        List<Run> joined = new ArrayList<>();
        for (Run each : sorted) {
            Run last = joined.isEmpty() ? null : joined.getLast();
            if (last != null && (last.longest() == null || last.longest() + 1 >= each.shortest())) {
                Long most = last.longest() == null || each.longest() == null ? null
                        : Long.valueOf(Math.max(last.longest(), each.longest()));
                joined.set(joined.size() - 1, new Run(last.shortest(), most));
            } else {
                joined.add(each);
            }
        }
        runs = List.copyOf(joined);
    }

    /** Every value of {@code values}, whatever its length. */
    public static ValuesAtLengths all(ValueSet values) {
        return new ValuesAtLengths(values, List.of(EVERY));
    }

    /** The values {@code within} holds, at the one run of lengths it holds them to. */
    public static ValuesAtLengths of(ValuesWithin within) {
        return new ValuesAtLengths(within.values(), List.of(Run.of(within)));
    }

    /** The values of {@code values} at any of the runs {@code each} holds its own to. */
    public static ValuesAtLengths atAnyOf(ValueSet values, List<ValuesWithin> each) {
        return new ValuesAtLengths(values, each.stream().map(Run::of).toList());
    }

    /** Whether a length bounds these beside the set. */
    public boolean bounded() {
        return !runs.equals(List.of(EVERY));
    }

    /** The values of {@code narrowed}, which is the set met with something, at these lengths. */
    public ValuesAtLengths over(ValueSet narrowed) {
        return new ValuesAtLengths(narrowed, runs);
    }

    /** The values in both, where {@code narrowed} is what the two sets met to. */
    public ValuesAtLengths meeting(ValuesAtLengths other, ValueSet narrowed) {
        List<Run> both = new ArrayList<>();
        for (Run mine : runs) {
            for (Run theirs : other.runs) {
                Run shared = mine.and(theirs);
                if (shared != null) {
                    both.add(shared);
                }
            }
        }
        return new ValuesAtLengths(both.isEmpty() ? ValueSet.NONE : narrowed, both);
    }

    /** The values of each run, each as the values of the set at that run. */
    public List<ValuesWithin> pieces() {
        return runs.stream()
                .map(each -> new ValuesWithin(values, each.shortest(), each.longest())).toList();
    }

    /** Whether {@code value} is one of these. */
    public boolean has(Value value) {
        return pieces().stream().anyMatch(each -> each.has(value));
    }

    /** Whether one of these is shown to be a value: one of some run is
     *  ({@link ValuesWithin#shownToHoldAValue}). */
    public boolean shownToHoldAValue() {
        return pieces().stream().anyMatch(ValuesWithin::shownToHoldAValue);
    }

    /** Whether none of these is shown to be one: none of any run is. */
    public boolean shownToHoldNone() {
        return pieces().stream().allMatch(ValuesWithin::shownToHoldNone);
    }
}
