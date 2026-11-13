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
import souther.compiler.values.Sets;
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
     * What a position holds of its strings: the set it admits with the ends of their lengths, and
     * the lengths its rules take out from between those ends.
     *
     * <p>Two things and not one set, because they are asked at different costs. The ends are
     * numbers and stay numbers for whatever reads them so; the lengths taken out are taken out of
     * the strings only by a reader that needs the strings as one set ({@link #asOneSet}), which
     * pays for a machine as long as the lengths and says what stopped it where it cannot. A reader
     * of {@link #within} alone, with the lengths taken out not asked, holds more strings than the
     * position does, so {@link #hasHoles} says whether it may.
     *
     * @param within the set the position admits, held to the ends of the lengths its rules leave
     * @param runs   the runs of lengths that are all of them, where the rules take some out from
     *               between the ends — two or more, lowest first — and null where they take none
     */
    record Held(ValuesWithin within, List<NumericDomain.Bounds> runs) {

        Held {
            if (within == null) {
                throw new IllegalArgumentException("a position holds the strings of some set");
            }
            if (runs != null && runs.size() < 2) {
                throw new IllegalArgumentException(
                        "lengths taken out from between the ends are two runs or more");
            }
            runs = runs == null ? null : List.copyOf(runs);
        }

        /** Strings of one run of lengths, which the ends say. */
        static Held ofOneRun(ValuesWithin within) {
            return new Held(within, null);
        }

        /** Whether the rules take lengths out from between the ends of {@link #within}. */
        boolean hasHoles() {
            return runs != null;
        }
    }

    /**
     * The strings {@code at} holds, or null where they are not shown to be all of them.
     *
     * <p>Null is that nothing is shown, and not that the position holds more.
     */
    static Held held(Position at) {
        ValueSet admitted = at.admitted().approximation();
        boolean whole = at.admitted().completeness()
                instanceof AdmissibleSet.Completeness.Complete;
        if (!whole && !boundsAreTheWholeOfTheRules(at)) {
            return null;
        }
        LengthsPastTheWay.Lengths left = lengthsLeft(at);
        if (left == null) {
            return whole ? Held.ofOneRun(ValuesWithin.all(admitted)) : null;
        }
        // What the rules leave the length, which is not always what their ends say: lengths taken
        // out from between the ends are runs of their own, and one run that is not the run between
        // the ends is where the ends are no longer the lengths a string may have. Both are the
        // lengths the position holds, and the ends are held to them.
        List<NumericDomain.Bounds> runs = runsOfTheLengths(at);
        if (runs != null) {
            if (runs.isEmpty()) {
                return null;
            }
            LengthsPastTheWay.Lengths ofTheRuns =
                    lengthsOf(new NumericDomain.Bounds(runs.getFirst().min(), runs.getLast().max()));
            if (ofTheRuns == null) {
                return null;
            }
            ValuesWithin within = left.and(ofTheRuns).over(admitted);
            return runs.size() == 1 ? Held.ofOneRun(within) : new Held(within, runs);
        }
        // Where the set admitted already counts the code points and says nothing else, what it
        // says is the lengths, which are held as numbers in its place.
        if (!left.isEvery() && isEveryStringOf(admitted, left)) {
            return Held.ofOneRun(left.over(ValueSet.ANY));
        }
        return Held.ofOneRun(whole ? ValuesWithin.all(admitted) : left.over(admitted));
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
     * <p>The bounds are two ends, and a hole between them is a rule they do not state. Where the
     * runs of the length are held beside the ends ({@link PositionBounds#runsLeft}), the ends and
     * the runs are the whole of what the rules say of the length, which the owner of the rules
     * only says where nothing else stands in the way; they are taken out of the strings below.
     */
    static boolean boundsAreTheWholeOfTheRules(Position at) {
        if (at.projection() instanceof ProjectionEvidence.CertifiedExact) {
            return true;
        }
        List<NumericDomain.Bounds> runs = runsOfTheLengths(at);
        return runs != null && !runs.isEmpty();
    }

    /**
     * The lengths of the strings {@code held} holds, as the runs of whole numbers they lie in, or
     * null where an end of a run is no whole count.
     */
    static LengthRuns lengthRunsOf(Held held) {
        LengthRuns between = LengthRuns.of(held.within());
        if (!held.hasHoles()) {
            return between;
        }
        List<LengthsPastTheWay.Lengths> runs = new ArrayList<>();
        for (NumericDomain.Bounds run : held.runs()) {
            LengthsPastTheWay.Lengths lengths = lengthsOf(run);
            if (lengths == null) {
                return null;
            }
            runs.add(lengths);
        }
        return between.and(LengthRuns.ofAll(runs));
    }

    /**
     * The runs of lengths the rules of {@code at} leave a string of it where they are not the run
     * between the ends, or null where they are. Empty where the rules of more than one number say
     * so, which is not worked out here.
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
     * {@code admitted} met with the strings whose length is in one of {@code runs}, or null where
     * that is not made: a run whose ends are no whole count, or strings of those lengths that are
     * a machine past what {@code meter} allows, which {@code meter} then says.
     *
     * <p>Null at every step and never a set made of what came before it. A machine this compiler
     * could not afford says nothing of the strings, and a set built from some of the runs is a set
     * short of the others. The meet itself is the table every pair of sets is met by
     * ({@link Sets#metUnder}), which is what takes a set of every string but a few as well as a
     * language.
     */
    private static ValueSet withoutTheLengthsBetween(ValueSet admitted,
                                                     List<NumericDomain.Bounds> runs,
                                                     Meter meter) {
        Language ofTheRuns = null;
        for (NumericDomain.Bounds run : runs) {
            LengthsPastTheWay.Lengths lengths = lengthsOf(run);
            Language here = lengths == null ? null
                    : Partitions.ofTheLengths(Language.EVERY_STRING, lengths, meter);
            if (here == null) {
                return null;
            }
            ofTheRuns = ofTheRuns == null ? here : ofTheRuns.or(here, meter);
            if (ofTheRuns == null) {
                return null;
            }
        }
        return ofTheRuns == null ? null
                : Sets.metUnder(admitted, ValueSet.matching(ofTheRuns), meter);
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
    static ValueSet asOneSet(Held held, Meter meter) {
        return held.hasHoles()
                ? withoutTheLengthsBetween(held.within().values(), held.runs(), meter)
                : asOneSet(held.within(), meter);
    }

    private static ValueSet asOneSet(ValuesWithin held, Meter meter) {
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
        Held held = held(at);
        // A function of the strings, the lengths and the lengths taken out alone, asked of every
        // relation a reading reads the position in, and as long to make as the lengths are: made
        // once for the reading.
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
