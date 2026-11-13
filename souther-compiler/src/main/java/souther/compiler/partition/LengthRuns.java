package souther.compiler.partition;

import souther.compiler.values.ValueSet;
import souther.compiler.values.ValuesAtLengths;
import souther.compiler.values.ValuesWithin;
import souther.compiler.regex.PatternPlan;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * The lengths a string may have, as the runs of whole numbers they lie in.
 *
 * <p>{@link LengthsPastTheWay.Lengths} is one run, and the lengths a rule takes out from between
 * its ends are runs beside one another: {@code String.length(value) /= 7} leaves up to six and
 * eight and over. Held as the numbers they are, a hole costs one run more however long the
 * strings it is taken out of, where the strings of the runs made into one set are a machine as
 * long as the longest of them.
 *
 * <p>Lowest first and apart from each other, with a length between each run and the next that
 * neither holds — runs that overlap or touch are one run — and none that holds no length. Made only
 * by the factories here, which put what they are handed into that shape, so every question below
 * can take it for granted and two of these holding the same lengths are equal. No runs at all is
 * no length ({@link #isEmpty}), and the one run of every length is {@link #EVERY}.
 *
 * <p>The same questions {@link LengthsPastTheWay.Lengths} answers, of each run and put together,
 * so that a reader of one run is a reader of these where there is one.
 *
 * @param runs the runs, lowest first
 */
record LengthRuns(List<LengthsPastTheWay.Lengths> runs) implements StringsPastTheWay {

    LengthRuns {
        runs = List.copyOf(runs);
    }

    /** Every length a string has. */
    static final LengthRuns EVERY = new LengthRuns(List.of(LengthsPastTheWay.Lengths.EVERY));

    /** No length at all. */
    static final LengthRuns NONE = new LengthRuns(List.of());

    /** The lengths of one run, or none where it holds none. */
    static LengthRuns of(LengthsPastTheWay.Lengths one) {
        return one.isEmpty() ? NONE : new LengthRuns(List.of(one));
    }

    /** The lengths a string of {@code within} is held to, as one run. */
    static LengthRuns of(ValuesWithin within) {
        return of(LengthsPastTheWay.Lengths.of(within));
    }

    /**
     * The lengths of all of {@code runs} together, in the shape above: lowest first, those that
     * overlap or touch as one, and none of those that hold no length.
     */
    static LengthRuns ofAll(List<LengthsPastTheWay.Lengths> runs) {
        List<LengthsPastTheWay.Lengths> held = new ArrayList<>();
        for (LengthsPastTheWay.Lengths each : runs) {
            if (!each.isEmpty()) {
                held.add(each);
            }
        }
        held.sort(Comparator.comparing(LengthsPastTheWay.Lengths::least));
        List<LengthsPastTheWay.Lengths> out = new ArrayList<>();
        for (LengthsPastTheWay.Lengths each : held) {
            LengthsPastTheWay.Lengths last = out.isEmpty() ? null : out.getLast();
            if (last != null && last.most().add(BigInteger.ONE).compareTo(each.least()) >= 0) {
                out.set(out.size() - 1, new LengthsPastTheWay.Lengths(last.least(),
                        last.most().max(each.most())));
            } else {
                out.add(each);
            }
        }
        return new LengthRuns(out);
    }

    /** These as {@code lengths} is, where it is some lengths, or null where it is a count of
     *  something else. */
    static LengthRuns asRuns(StringsPastTheWay lengths) {
        return switch (lengths) {
            case LengthRuns it -> it;
            case LengthsPastTheWay.Lengths it -> of(it);
            case CodePointsPastTheWay _ -> null;
        };
    }

    /**
     * These as they are held where they are one run or none: the one {@link
     * LengthsPastTheWay.Lengths} a reader of one run holds, so that the same lengths are one value
     * however they were made. Several runs are held as these.
     */
    StringsPastTheWay canonical() {
        return runs.size() > 1 ? this
                : runs.isEmpty() ? new LengthsPastTheWay.Lengths(BigInteger.ONE, BigInteger.ZERO)
                : runs.getFirst();
    }

    /** Whether no string has a length of these. */
    @Override
    public boolean isEmpty() {
        return runs.isEmpty();
    }

    /** Whether a string of {@code length} code points has a length of these. */
    boolean holds(BigInteger length) {
        return runs.stream().anyMatch(each -> each.holds(length, length));
    }

    /** Whether every length a string has is one of these. */
    boolean isEvery() {
        return runs.size() == 1 && runs.getFirst().isEvery();
    }

    /** The lengths that are both these and {@code other}: each run of one met with each run of
     *  the other. */
    LengthRuns and(LengthRuns other) {
        List<LengthsPastTheWay.Lengths> both = new ArrayList<>();
        for (LengthsPastTheWay.Lengths mine : runs) {
            for (LengthsPastTheWay.Lengths theirs : other.runs) {
                both.add(mine.and(theirs));
            }
        }
        return ofAll(both);
    }

    /**
     * The values of {@code values} of each run of these, each as long as its run. None where no
     * string has a length of these.
     */
    List<ValuesWithin> over(ValueSet values) {
        return runs.stream().map(each -> each.over(values)).toList();
    }

    /** The values of {@code values} of these lengths, which is {@link #over} as one value. */
    ValuesAtLengths ofValues(ValueSet values) {
        return runs.isEmpty() ? ValuesAtLengths.all(ValueSet.NONE)
                : ValuesAtLengths.atAnyOf(values, over(values));
    }

    /**
     * The strings of every other length, each as long as it is left open at: those short of the
     * least of these, those between one run and the next, and those longer than the most. Every
     * string where there is no length of these.
     */
    List<ValuesWithin> outside() {
        if (runs.isEmpty()) {
            return List.of(ValuesWithin.all(ValueSet.ANY));
        }
        return gaps().stream().map(gap -> gap.over(ValueSet.ANY)).toList();
    }

    /** The runs of the lengths these do not hold, lowest first. */
    private List<LengthsPastTheWay.Lengths> gaps() {
        List<LengthsPastTheWay.Lengths> out = new ArrayList<>();
        BigInteger next = BigInteger.ZERO;
        for (LengthsPastTheWay.Lengths each : runs) {
            if (each.least().compareTo(next) > 0) {
                out.add(new LengthsPastTheWay.Lengths(next, each.least().subtract(BigInteger.ONE)));
            }
            next = each.most().add(BigInteger.ONE);
        }
        BigInteger longest = LengthsPastTheWay.Lengths.EVERY.most();
        if (next.compareTo(longest) <= 0) {
            out.add(new LengthsPastTheWay.Lengths(next, longest));
        }
        return out;
    }

    /**
     * The strings of these lengths, or null where there are none or the ends are past what a
     * pattern counts.
     */
    @Override
    public PatternPlan strings() {
        return joined(runs);
    }

    /**
     * The strings of every other length, or null where there are none or the ends are past what a
     * pattern counts.
     */
    @Override
    public PatternPlan stringsOutside() {
        return runs.isEmpty() ? null : joined(gaps());
    }

    /** The strings of any of {@code of}, or null where none is a length or an end is past what a
     *  pattern counts. */
    private static PatternPlan joined(List<LengthsPastTheWay.Lengths> of) {
        PatternPlan all = null;
        for (LengthsPastTheWay.Lengths each : of) {
            PatternPlan one = each.strings();
            if (one == null) {
                return null;
            }
            all = all == null ? one : all.or(one);
        }
        return all;
    }
}
