package souther.compiler.values;

import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.regex.Language;
import net.unit8.notation199x.pattern.Meter;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What two sets of values come to, and what making it costs.
 *
 * <p>The one table there is, and the one place the shapes are told apart. What each pair costs is
 * what it builds: a finite set is arithmetic over values in hand however it is paired, and two
 * languages are a machine. Written twice, the day one of them learned something the other did not
 * would be a day two readings of one model disagreed.
 *
 * <p><b>The table and nothing else.</b> Which position pays, whether one has been given up on, and
 * what order several of them are put together in are not here — they are questions about an answer
 * being built rather than about a pair of sets, and they belong to whoever is building it
 * ({@link Allowance}). Held here too, a caller with two sets in hand could put them together
 * wherever it happened to hold them, which is a fold in arrival order under another name.
 *
 * <p>Null where the allowance ran out, and never a smaller set. What a caller is told is that this
 * was not built, which is a fact about this compiler, and never that the rules leave less than they
 * do.
 */
public final class Sets {

    private Sets() {
    }

    /**
     * What two sets neither of which is a language come to, which costs nothing either way.
     *
     * <p>Here so that the arithmetic over values a rule wrote out is written once. A plan puts two
     * of them together while it is being normalised, where there is nothing to build and no meter
     * to spend; the table below reaches the same cases when a language is on one side. Written
     * twice, the day one of them learned something the other did not would be a day two readings of
     * one model disagreed.
     */
    static ValueSet metPlainly(ValueSet one, ValueSet other) {
        return plainly(one, other, true);
    }

    /** The same for a choice. */
    static ValueSet joinedPlainly(ValueSet one, ValueSet other) {
        return plainly(one, other, false);
    }

    private static ValueSet plainly(ValueSet one, ValueSet other, boolean met) {
        if (one instanceof ValueSet.Matching || other instanceof ValueSet.Matching) {
            throw new IllegalArgumentException(
                    "a language is put together where there is an allowance for it");
        }
        // The table below takes a meter because a pair with a language in it builds; the pairs
        // above have none and reach no case that does. Which is a fact about the pairs and not a
        // promise anybody keeps, so what is handed over is a meter that pays for nothing
        // ({@link Meter#refusing}): the day a language reaches here, the state it asks for is
        // refused where it is asked for rather than made out of an allowance nobody granted.
        return met ? metUnder(one, other, Meter.refusing())
                : joinedUnder(one, other, Meter.refusing());
    }

    /**
     * The values both admit, or null where making them ran past what {@code meter} allows.
     *
     * <p>The one table there is, and the one place the shapes are told apart. What each pair costs
     * is what it builds: a finite set is arithmetic over values in hand however it is paired, and
     * two languages are a machine.
     */
    public static ValueSet metUnder(ValueSet one, ValueSet other, Meter meter) {
        return switch (one) {
            case ValueSet.Finite here -> switch (other) {
                case ValueSet.Finite there -> new ValueSet.Finite(
                        kept(here.values(), there.values()::contains));
                case ValueSet.Cofinite there -> new ValueSet.Finite(
                        kept(here.values(), each -> !there.excluded().contains(each)));
                // Which of finitely many the language holds, asked of each. Exact and free: what
                // comes out is a subset of what was already written down, so no machine is made.
                case ValueSet.Matching there -> new ValueSet.Finite(
                        kept(here.values(), there::has));
                // The same, of runs: which of them a run holds is its ends against the value.
                case ValueSet.WholeRuns there -> new ValueSet.Finite(
                        kept(here.values(), there::has));
            };
            case ValueSet.Cofinite here -> switch (other) {
                case ValueSet.Finite _ -> metUnder(other, one, meter);
                case ValueSet.Cofinite there ->
                        new ValueSet.Cofinite(both(here.excluded(), there.excluded()));
                case ValueSet.Matching _ -> metUnder(other, one, meter);
                // The runs with each whole number left out cut out of them, which is runs: a
                // number left out is one more end on each side of it.
                case ValueSet.WholeRuns there -> ValueSet.wholeNumbers(
                        there.numbers().and(wholeNumbersIn(here.excluded()).others()));
            };
            case ValueSet.Matching here -> switch (other) {
                case ValueSet.Finite there -> new ValueSet.Finite(
                        kept(there.values(), here::has));
                // The language less what is excluded, which is a language: a value written out is
                // a string the machine can be told to refuse, and the rest is untouched.
                case ValueSet.Cofinite there ->
                        matching(here.language().without(textsIn(there.excluded()), meter));
                case ValueSet.Matching there ->
                        matching(here.language().and(there.language(), meter));
                // Strings and whole numbers share no value.
                case ValueSet.WholeRuns _ -> ValueSet.NONE;
            };
            case ValueSet.WholeRuns here -> switch (other) {
                case ValueSet.Finite _, ValueSet.Cofinite _, ValueSet.Matching _ ->
                        metUnder(other, one, meter);
                // What both hold is read off the ends of both, however many numbers they hold.
                case ValueSet.WholeRuns there ->
                        ValueSet.wholeNumbers(here.numbers().and(there.numbers()));
            };
        };
    }

    /** The values either admits, on the same terms. */
    public static ValueSet joinedUnder(ValueSet one, ValueSet other, Meter meter) {
        return switch (one) {
            case ValueSet.Finite here -> switch (other) {
                case ValueSet.Finite there ->
                        new ValueSet.Finite(both(here.values(), there.values()));
                // Everything the other admits, less what it excludes and this does not have: a
                // value it excludes is admitted here where this names it, so it is no longer
                // excluded from the two of them together.
                case ValueSet.Cofinite there -> new ValueSet.Cofinite(
                        kept(there.excluded(), each -> !here.values().contains(each)));
                case ValueSet.Matching _, ValueSet.WholeRuns _ -> joinedUnder(other, one, meter);
            };
            case ValueSet.Cofinite here -> switch (other) {
                case ValueSet.Finite _ -> joinedUnder(other, one, meter);
                case ValueSet.Cofinite there -> new ValueSet.Cofinite(
                        kept(here.excluded(), there.excluded()::contains));
                case ValueSet.Matching _, ValueSet.WholeRuns _ -> joinedUnder(other, one, meter);
            };
            case ValueSet.Matching here -> switch (other) {
                // The language and the values written beside it, which is a language: what a set of
                // words costs to add is the words.
                case ValueSet.Finite there ->
                        matching(here.language().with(textsIn(there.values()), meter));
                // Everything except what is excluded and the language does not hold. A value
                // excluded there is admitted here where the language holds it, so it is excluded
                // from the two of them together only where neither has it — which is asked of each
                // of finitely many and builds nothing.
                case ValueSet.Cofinite there -> new ValueSet.Cofinite(
                        kept(there.excluded(), each -> !here.has(each)));
                case ValueSet.Matching there ->
                        matching(here.language().or(there.language(), meter));
                // Strings and whole numbers, which no one shape holds together: every value, which
                // holds both and refuses nothing either side admits.
                case ValueSet.WholeRuns _ -> ValueSet.ANY;
            };
            case ValueSet.WholeRuns here -> switch (other) {
                // The runs with the whole numbers written beside them, each a run of its own —
                // and every value where one written there is no whole number, for the same reason.
                case ValueSet.Finite there -> there.values().stream()
                        .allMatch(each -> ValueSet.wholeNumberOf(each) != null)
                        ? ValueSet.wholeNumbers(here.numbers().or(wholeNumbersIn(there.values())))
                        : ValueSet.ANY;
                // Everything but what is excluded there and in none of the runs.
                case ValueSet.Cofinite there -> new ValueSet.Cofinite(
                        kept(there.excluded(), each -> !here.has(each)));
                case ValueSet.Matching _ -> joinedUnder(other, one, meter);
                case ValueSet.WholeRuns there ->
                        ValueSet.wholeNumbers(here.numbers().or(there.numbers()));
            };
        };
    }

    /** The whole numbers among {@code values}, each a run of its own; a value that is no whole
     *  number is in no run. */
    private static WholeNumberRuns wholeNumbersIn(Set<Value> values) {
        List<BigInteger> out = new ArrayList<>();
        values.forEach(each -> {
            BigInteger whole = ValueSet.wholeNumberOf(each);
            if (whole != null) {
                out.add(whole);
            }
        });
        return WholeNumberRuns.of(out);
    }

    /** The set a language came to, or null where it was not built. */
    private static ValueSet matching(Language made) {
        return made == null ? null : ValueSet.matching(made);
    }


    /** The strings among {@code values}, which are the only ones a language has a word for. */
    static Set<String> textsIn(Set<Value> values) {
        Set<String> out = new LinkedHashSet<>();
        values.forEach(each -> {
            if (each instanceof Value.Text text) {
                out.add(text.value());
            }
        });
        return out;
    }

    private static Set<Value> kept(Set<Value> these, java.util.function.Predicate<Value> keep) {
        Set<Value> out = new LinkedHashSet<>();
        these.forEach(each -> {
            if (keep.test(each)) {
                out.add(each);
            }
        });
        return out;
    }

    private static Set<Value> both(Set<Value> these, Set<Value> those) {
        Set<Value> out = new LinkedHashSet<>(these);
        out.addAll(those);
        return out;
    }
}
