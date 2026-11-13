package souther.compiler.partition;

import souther.compiler.inputs.SearchRegion;
import souther.compiler.regex.Language;
import souther.compiler.regex.StringsOfAPiece;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.values.ValueSet;

import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * What one reading of a body's guards works out once and hands back to whoever asks the same
 * again while the reading lasts: the walk of a way ({@link WayToTheBorder#along}), what a run's
 * answers narrow a region by ({@link Reachability.Reaching#narrowedPast}), what a statement
 * says of its remainder ({@link ARemainderMoved#saidBy}), which operations of a case conversion
 * are not exact over the strings it is done to ({@link #notExactOver}), what it answers of them
 * ({@link #conversionAnswers}), which pieces of what
 * it answers are pieces of its values ({@link #piecesAConversionAnswers}), whether the strings
 * a position admits are every string of the lengths its rules leave it ({@link #everyStringOf}),
 * and those strings made into one set ({@link #stringsAsOneSet}).
 *
 * <p>A reading reads one way over many regions and for many relations, each building the way afresh
 * from the same conditions; and it takes the way to each case, and each way that is split into,
 * past what the run to the border got past working out, where ways that differ only in what no
 * region says — truths, cases — share one region. And the walks of those ways take each statement
 * of a remainder in along every way of the choices before it, and the readers that hold one
 * statement of a remainder against another ask it of each pair. All are functions of what they are
 * asked alone. A walk is of the conditions on the way: one vocabulary reads them and constants
 * stop it, and the declarations do not enter it. A narrowing is of the region and the answers.
 * What a statement says of its remainder is of the statement.
 *
 * <p><b>The same things, and not equal ones.</b> Asked by identity. What a walk hands back names
 * the choices it made by the entry they were made at, and its readers look them up by identity, so
 * a walk of conditions equal to these but not these would name entries the asker does not hold. And
 * telling one region from another by identity costs nothing beside the narrowing it saves; a region
 * equal to one asked before but another value is narrowed for itself, to the same answer.
 *
 * <p><b>Held by the reading and by nothing it answers.</b> What comes back is what was worked out
 * — a walk with the figure that stopped it and the order of its ways — so an asker cannot tell an
 * answer handed back from one worked out for it. Everything is kept while the reading lasts, which
 * is no more than it asked, and let go when it ends. Any figure an asker counts its asking by is its
 * own. Outside a reading everything is worked out when it is asked.
 */
final class OneReading {

    private static final ScopedValue<OneReading> READING = ScopedValue.newInstance();

    private final Map<Conditions, OneOfEach.Walked<OnTheWay, Reachability>> walked =
            new HashMap<>();
    private final Map<RegionPast, Reachability.Reaching.NarrowedPast> narrowed = new HashMap<>();
    private final Map<RowDemand.OnARemainder, Optional<ARemainderMoved.Said>> remaindersSaid =
            new IdentityHashMap<>();
    /** By value: a conversion is a value, and a language is its strings, hashed off the table it
     *  was made into when it was made. */
    private final Map<ConvertedOver, List<String>> notExact = new HashMap<>();
    /** By value, for the same reason. */
    private final Map<PiecesAsked, Optional<PiecesAnswered>> piecesAnswered = new HashMap<>();
    /** By value, for the same reason: what a conversion answers of the strings of a language. */
    private final Map<ConvertedOver, Optional<WhatAConversionAnswers>> conversionAnswers =
            new HashMap<>();
    /** By value, for the same reason: a set of strings and some lengths. */
    private final Map<LengthsOver, Boolean> everyStringOfTheLengths = new HashMap<>();
    /** By value, for the same reason: a set of strings, the lengths held beside it, and the
     *  lengths taken out from between them. */
    private final Map<StringsHeld.Held, Optional<ValueSet>> asOneSet = new HashMap<>();

    private OneReading() {
    }

    /** What {@code reading} comes to, each thing it asks to have worked out worked out once. */
    static <T> T over(Supplier<T> reading) {
        return ScopedValue.where(READING, new OneReading()).call(reading::get);
    }

    /** The walk of {@code onTheWay}: the one this reading walked already, or {@code walking}'s,
     *  walked now. */
    static OneOfEach.Walked<OnTheWay, Reachability> walked(
            List<OnTheWay> onTheWay, Supplier<OneOfEach.Walked<OnTheWay, Reachability>> walking) {
        return READING.isBound()
                ? kept(READING.get().walked, new Conditions(onTheWay), walking)
                : walking.get();
    }

    /** What {@code answered} narrows {@code region} by: as this reading narrowed it already, or
     *  {@code narrowing}'s, now. */
    static Reachability.Reaching.NarrowedPast narrowedPast(
            SearchRegion region, DemandReading.Answered answered,
            Supplier<Reachability.Reaching.NarrowedPast> narrowing) {
        return READING.isBound()
                ? kept(READING.get().narrowed, new RegionPast(region, answered), narrowing)
                : narrowing.get();
    }

    /** What {@code statement} says of its remainder: as this reading read it already, or
     *  {@code reading}'s, now. */
    static Optional<ARemainderMoved.Said> remainderSaidBy(
            RowDemand.OnARemainder statement, Supplier<Optional<ARemainderMoved.Said>> reading) {
        return READING.isBound()
                ? kept(READING.get().remaindersSaid, statement, reading)
                : reading.get();
    }

    /** The operations of {@code conversion} whose image is not shown over {@code over}: as this
     *  reading worked them out already, or {@code working}'s, now. */
    static List<String> notExactOver(CaseMapping conversion, Language over,
                                     Supplier<List<String>> working) {
        return READING.isBound()
                ? kept(READING.get().notExact, new ConvertedOver(conversion, over), working)
                : working.get();
    }

    /** What {@code conversion} answers of the strings of {@code over}, or null where the machines
     *  for them are past the allowance: as this reading worked it out already, or
     *  {@code working}'s, now. */
    static WhatAConversionAnswers conversionAnswers(CaseMapping conversion, Language over,
                                                    Supplier<WhatAConversionAnswers> working) {
        return READING.isBound()
                ? kept(READING.get().conversionAnswers, new ConvertedOver(conversion, over),
                        () -> Optional.ofNullable(working.get())).orElse(null)
                : working.get();
    }

    /** The pieces of what {@code conversion} answers of {@code whole} at {@code separator} in
     *  {@code window}: as this reading worked them out already, or {@code working}'s, now. */
    static Optional<PiecesAnswered> piecesAConversionAnswers(
            int separator, PieceWindow window, CaseMapping conversion, Language whole,
            Supplier<Optional<PiecesAnswered>> working) {
        return READING.isBound()
                ? kept(READING.get().piecesAnswered,
                        new PiecesAsked(separator, window, conversion, whole), working)
                : working.get();
    }

    /** Whether {@code strings} is every string of {@code lengths}: as this reading worked it out
     *  already, or {@code working}'s, now. */
    static boolean everyStringOf(Language strings, LengthsPastTheWay.Lengths lengths,
                                 Supplier<Boolean> working) {
        return READING.isBound()
                ? kept(READING.get().everyStringOfTheLengths,
                        new LengthsOver(strings, lengths), working)
                : working.get();
    }

    /** The strings {@code held} holds as one set within the allowance of a piece of a language,
     *  or null where they are none: as this reading made it already, or {@code working}'s, now. */
    static ValueSet stringsAsOneSet(StringsHeld.Held held, Supplier<ValueSet> working) {
        return READING.isBound()
                ? kept(READING.get().asOneSet, held, () -> Optional.ofNullable(working.get()))
                        .orElse(null)
                : working.get();
    }

    /** The pieces of a conversion's answers that are pieces of its values, and what a piece may be
     *  besides. */
    record PiecesAnswered(StringsOfAPiece.Shown shown, Language mayBe) {}

    /** The answer kept in {@code in} for {@code asked}, or {@code working}'s, kept from now on.
     *  Looked up and put in apart, so working one out may ask for another. */
    private static <K, V> V kept(Map<K, V> in, K asked, Supplier<V> working) {
        V known = in.get(asked);
        if (known != null) {
            return known;
        }
        V made = working.get();
        in.put(asked, made);
        return made;
    }

    /** The conditions on a way, in their order, each by identity. */
    private static final class Conditions {

        private final List<OnTheWay> entries;
        private final int hash;

        Conditions(List<OnTheWay> entries) {
            this.entries = entries;
            int out = 1;
            for (OnTheWay each : entries) {
                out = 31 * out + System.identityHashCode(each);
            }
            this.hash = out;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof Conditions that) || hash != that.hash
                    || entries.size() != that.entries.size()) {
                return false;
            }
            for (int at = 0; at < entries.size(); at++) {
                if (entries.get(at) != that.entries.get(at)) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    /** A region and the answers it is narrowed by, each by identity. */
    private static final class RegionPast {

        private final SearchRegion region;
        private final DemandReading.Answered answered;

        RegionPast(SearchRegion region, DemandReading.Answered answered) {
            this.region = region;
            this.answered = answered;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof RegionPast that && region == that.region
                    && answered == that.answered;
        }

        @Override
        public int hashCode() {
            return 31 * System.identityHashCode(region) + System.identityHashCode(answered);
        }
    }

    /** A conversion and the strings it is done to. */
    private record ConvertedOver(CaseMapping conversion, Language over) {}

    /** Some strings and the lengths they are asked to be every string of. */
    private record LengthsOver(Language strings, LengthsPastTheWay.Lengths lengths) {}

    /** Which pieces of what a conversion answers of some strings are asked for. */
    private record PiecesAsked(int separator, PieceWindow window, CaseMapping conversion,
                               Language whole) {}
}
