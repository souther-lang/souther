package souther.compiler.partition;

import souther.compiler.check.ProjectionEvidence;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionBounds;
import souther.compiler.inputs.RepresentationBounds;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;
import souther.compiler.values.ValuesWithin;

import net.unit8.notation199x.pattern.Meter;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The strings a position holds, as far as they are shown to be all of them.
 *
 * <p>A position's set of values is read from the rules about its strings, and a rule about the
 * length of a string is a bound on a number the set does not read. Such a position is left wider
 * than it is by the set alone, and the bounds on the length are the rest of what the rules say: the
 * strings it holds are the strings of the set that have a length the bounds leave. That is shown
 * only where the bounds are shown to be the whole of the rules and the length is the one number
 * they bound. Otherwise nothing is said of the strings.
 *
 * <p>The lengths are held as the numbers they are, beside the set ({@link #within}). Made into
 * one set of strings, every string up to a length is a machine with a state for each code point
 * of it, so a rule naming a long length would be one this compiler refuses to read; a reader that
 * reads the length as a number asks nothing of that size, and one that needs the strings as one
 * set makes them ({@link #asOneSet}).
 *
 * <p>Asked in one place, so that what a relation is read over is the same strings wherever it is
 * asked.
 */
final class StringsHeld {

    private StringsHeld() { }

    /**
     * The strings {@code at} holds, as the set it admits and the lengths its rules leave a string
     * of it, or null where they are not shown to be all of them.
     *
     * <p>Null is that nothing is shown, and not that the position holds more.
     */
    static ValuesWithin within(Position at) {
        ValueSet admitted = at.admitted().approximation();
        boolean whole = at.admitted().completeness()
                instanceof AdmissibleSet.Completeness.Complete;
        if (!whole && !boundsAreTheWholeOfTheRules(at)) {
            return null;
        }
        LengthsPastTheWay.Lengths left = lengthsLeft(at);
        if (left == null) {
            return whole ? ValuesWithin.all(admitted) : null;
        }
        // Lengths the rules take out from between their ends are not what the ends say. The ends
        // are held as numbers, and the lengths taken out are taken out of the set: a string of one
        // of them is no string the position holds. Where that set is no machine this compiler
        // makes within the allowance, the strings are not shown.
        List<NumericDomain.Bounds> runs = runsOfTheLengths(at);
        if (runs != null) {
            admitted = withoutTheLengthsBetween(admitted, runs);
            if (admitted == null) {
                return null;
            }
            return left.over(admitted);
        }
        // Where the set admitted already counts the code points and says nothing else, what it
        // says is the lengths, which are held as numbers in its place.
        if (!left.isEvery() && isEveryStringOf(admitted, left)) {
            return left.over(ValueSet.ANY);
        }
        return whole ? ValuesWithin.all(admitted) : left.over(admitted);
    }

    /**
     * The lengths the rules of {@code at} leave a string of it, or null where a rule about its
     * length is not read as one: an end that is no whole count, or a rule that bounds another
     * number beside it.
     */
    private static LengthsPastTheWay.Lengths lengthsLeft(Position at) {
        LengthsPastTheWay.Lengths left = LengthsPastTheWay.Lengths.EVERY;
        for (PositionBounds each : at.bounds()) {
            if (!(each.term() instanceof NumericTerm.TakenOf taken)
                    || !RepresentationBounds.isALength(taken)) {
                continue;
            }
            LengthsPastTheWay.Lengths lengths = lengthsOf(each.rangeLeft());
            if (lengths == null || !StringsReached.bindsNothing(at, each)) {
                return null;
            }
            left = left.and(lengths);
        }
        return left;
    }

    /**
     * Whether the bounds of {@code at} are shown to be the whole of what its rules leave, with the
     * lengths the rules take out from between the ends held as the runs that they are.
     *
     * <p>The bounds are two ends, and a hole between them is a rule they do not state; that is all
     * that stands in the way where the one number that has a hole is the length, whose runs are
     * held beside its ends ({@link PositionBounds#runsLeft}) and taken out of the strings below.
     * Any other cause, or a hole of another number, is still a rule nothing here states.
     */
    static boolean boundsAreTheWholeOfTheRules(Position at) {
        if (at.projection() instanceof ProjectionEvidence.CertifiedExact) {
            return true;
        }
        if (!(at.projection() instanceof ProjectionEvidence.NotCertified(var causes))) {
            return false;
        }        Set<Object> holed = new LinkedHashSet<>();
        for (ProjectionEvidence.Cause each : causes) {
            if (!(each instanceof ProjectionEvidence.Cause.Lossy lossy)
                    || !lossy.unstated().equals(Set.of(ProjectionEvidence.Cause.Unstated.A_HOLE))) {
                return false;
            }
            holed.add(lossy.atom());
        }
        List<NumericDomain.Bounds> runs = runsOfTheLengths(at);
        return holed.size() == 1 && runs != null && !runs.isEmpty();
    }

    /**
     * The runs of lengths the rules of {@code at} leave a string of it where they take some out
     * from between the ends, or null where they take none that was read.
     */
    private static List<NumericDomain.Bounds> runsOfTheLengths(Position at) {
        List<NumericDomain.Bounds> out = null;
        for (PositionBounds each : at.bounds()) {
            if (each.runsLeft() == null || !(each.term() instanceof NumericTerm.TakenOf taken)
                    || !RepresentationBounds.isALength(taken)) {
                continue;
            }
            if (out != null) {
                // Two numbers of one string that both leave holes: the strings are those of both,
                // which is not asked here.
                return List.of();
            }
            out = each.runsLeft().runs().stream()
                    .map(run -> new NumericDomain.Bounds(run.low(), run.high())).toList();
        }
        return out;
    }

    /**
     * {@code admitted} less the strings whose length is in none of {@code runs}, or null where
     * that is not worked out: a run whose ends are no whole count, or strings of those lengths
     * that are a machine past the allowance of a piece of a language.
     */
    private static ValueSet withoutTheLengthsBetween(ValueSet admitted,
                                                     List<NumericDomain.Bounds> runs) {
        if (runs.isEmpty()) {
            return null;
        }
        List<LengthsPastTheWay.Lengths> lengths = new ArrayList<>();
        for (NumericDomain.Bounds run : runs) {
            LengthsPastTheWay.Lengths of = lengthsOf(run);
            if (of == null) {
                return null;
            }
            lengths.add(of);
        }
        if (admitted instanceof ValueSet.Finite finite) {
            Set<Value> kept = new LinkedHashSet<>();
            for (Value each : finite.values()) {
                if (lengths.stream().anyMatch(run -> holds(run, each))) {
                    kept.add(each);
                }
            }
            return ValueSet.oneOf(kept);
        }
        Language language = UndividedByARelation.languageOf(admitted);
        if (language == null) {
            return null;
        }
        Meter meter = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
        Language of = null;
        for (LengthsPastTheWay.Lengths run : lengths) {
            Language here = Partitions.ofTheLengths(language, run, meter);
            if (here == null) {
                return null;
            }
            of = of == null ? here : of.or(here, meter);
        }
        return ValueSet.matching(of);
    }

    /** Whether {@code value} is a string of a length of {@code lengths}. */
    private static boolean holds(LengthsPastTheWay.Lengths lengths, Value value) {
        if (!(value instanceof Value.Text(String text))) {
            return false;
        }
        BigInteger count = BigInteger.valueOf(text.codePointCount(0, text.length()));
        return lengths.holds(count, count);
    }

    /**
     * Whether {@code admitted}, every value a position holds, is every string of the lengths
     * {@code left}: the set its declarations admit already counts the code points, and what the
     * rules say of them is the length and no other thing. Answered by the two being one set,
     * where the strings of the lengths are a machine within the allowance of a piece of a
     * language.
     */
    private static boolean isEveryStringOf(ValueSet admitted, LengthsPastTheWay.Lengths left) {
        if (!(admitted instanceof ValueSet.Matching(Language language))) {
            return false;
        }
        // A function of the two, asked of every relation a reading reads the position in, and
        // what it builds is as long as the length: worked out once for the reading.
        return OneReading.everyStringOf(language, left, () -> language.equals(
                Partitions.ofTheLengths(Language.EVERY_STRING, left,
                        PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter())));
    }

    /**
     * The strings of {@code held} as one set, or null where they are no set of strings this
     * compiler makes within {@code meter}: where the set is no language, or the strings of its
     * lengths are a machine past what {@code meter} allows, which {@code meter} then says.
     */
    static ValueSet asOneSet(ValuesWithin held, Meter meter) {
        if (!held.bounded()) {
            return held.values();
        }
        if (held.values() instanceof ValueSet.Finite finite) {
            Set<Value> kept = new LinkedHashSet<>();
            finite.values().stream().filter(held::has).forEach(kept::add);
            return ValueSet.oneOf(kept);
        }
        Language language = UndividedByARelation.languageOf(held.values());
        Language within = language == null ? null : Partitions.ofTheLengths(language,
                LengthsPastTheWay.Lengths.of(held), meter);
        return within == null ? null : ValueSet.matching(within);
    }

    /**
     * The strings {@code at} holds as one set ({@link #asOneSet}), or null where they are not
     * shown to be all of them or are no set made within the allowance of a piece of a language.
     */
    static ValueSet at(Position at) {
        ValuesWithin held = within(at);
        // A function of the strings and lengths alone, asked of every relation a reading reads the
        // position in, and as long to make as the lengths are: made once for the reading.
        return held == null ? null : OneReading.stringsAsOneSet(held,
                () -> asOneSet(held, PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter()));
    }

    /**
     * A bound on the code points of every string {@code at} holds, or null where nothing ends
     * them: the least of the end the rules leave its length ({@link HowManyAPlaceHolds}) and the
     * longest string of the set it admits.
     *
     * <p>No string {@code at} holds is longer, and none need be this long, so it asks for less
     * than {@link #at} does. The end a rule leaves the length holds of every value whether or not
     * the rules are read whole, and the set admitted is wider than the values in every reading
     * ({@link AdmissibleSet#approximation}); neither asks that the length be the one number bound.
     * The end is held as a number, so a length no language is written out to is still an end.
     */
    static BigInteger lengthBoundAt(Position at) {
        return leastOf(HowManyAPlaceHolds.atMost(at), longestOf(at.admitted().approximation()));
    }

    /** The longest string of {@code set}, or null where it has none or holds strings of every
     *  length. */
    private static BigInteger longestOf(ValueSet set) {
        return switch (set) {
            case ValueSet.Finite finite -> {
                BigInteger longest = BigInteger.ZERO;
                for (Value each : finite.values()) {
                    if (!(each instanceof Value.Text(String text))) {
                        yield null;
                    }
                    longest = longest.max(
                            BigInteger.valueOf(text.codePointCount(0, text.length())));
                }
                yield longest;
            }
            case ValueSet.Matching(Language language) -> {
                Language.Ends lengths = language.lengths();
                yield lengths == null || lengths.most() == null ? null
                        : BigInteger.valueOf(lengths.most());
            }
            case ValueSet.Cofinite _, ValueSet.WholeRuns _, ValueSet.WholeSteps _ -> null;
        };
    }

    /** The lesser of two ceilings, either of which may be none. */
    private static BigInteger leastOf(BigInteger one, BigInteger other) {
        return one == null ? other : other == null ? one : one.min(other);
    }

    /** The lengths {@code bounds} leave, or null where an end is not a whole count. */
    private static LengthsPastTheWay.Lengths lengthsOf(NumericDomain.Bounds bounds) {
        if (bounds == null) {
            return new LengthsPastTheWay.Lengths(null, null);
        }
        BigInteger least = null;
        BigInteger most = null;
        if (bounds.min() != null) {
            least = fewestFrom(bounds.min());
            if (least == null) {
                return null;
            }
        }
        if (bounds.max() != null) {
            most = HowManyAPlaceHolds.mostUpTo(bounds.max());
            if (most == null) {
                return null;
            }
        }
        return new LengthsPastTheWay.Lengths(least, most);
    }

    /** The fewest code points the end lets a string have, or null where it is no count. */
    private static BigInteger fewestFrom(Endpoint end) {
        if (!(end.at() instanceof Count count)
                || !(count.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger>(
                        BigInteger whole))) {
            return null;
        }
        return count.exactly().isWhole() && !end.inclusive() ? whole.add(BigInteger.ONE) : whole;
    }
}
