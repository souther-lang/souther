package souther.compiler.values;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.WholeNumberRuns;
import net.unit8.notation199x.pattern.Meter;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Which values one position may hold, as far as the rules about it were read.
 *
 * <p>Two shapes and not one, because {@code /=} does not leave a finite answer. {@code == "A"}
 * admits one value and {@code /= "A"} admits every value but one, and a reading with only the first
 * shape would have to answer the second with "anything" — which is true and is the answer that
 * loses {@code /= true} beside {@code /= false}. Written as the pair, the two are closed under
 * everything the connectives do to them.
 *
 * <p>{@link Cofinite} is over a carrier whose values are not counted out here. Where they can be
 * counted out — a boolean, an enumeration — what is excluded is taken away from them where the rule
 * is read, and what is left is a {@link Finite}. So a set that admits nothing is {@code Finite} with
 * nothing in it, and that is the only shape emptiness has: every reading that could reach it went
 * through values it had in hand.
 *
 * <p>{@link #ANY} is what a position nothing was read about holds, which is every value there is. It
 * is not "unread": whether a reading could take in the rules about a position is a separate answer
 * and is held separately ({@link AdmissibleValues}), because a position the model says nothing about
 * and a position this could not read say the same thing here and mean opposite things to a reader.
 *
 * <p><b>A set, and nothing about what it cost.</b> Two of these are put together by {@link Sets},
 * which is where the allowance for building a machine lives — so a set is a value wherever it came
 * from, and two equal sets are equal, but for the spellings {@link WholeRuns} says it keeps, which
 * {@link #holdsTheSameValuesAs} answers for. Written here, a meet would be an operation with no answer for
 * the case where the exact one is too much work, and the only thing left to do would be to fail in
 * the middle of a method that is supposed to be total.
 */
public sealed interface ValueSet {

    /** These values and no others. */
    record Finite(Set<Value> values) implements ValueSet {

        public Finite {
            values = held(values);
        }
    }

    /** Every value of the carrier except these. */
    record Cofinite(Set<Value> excluded) implements ValueSet {

        public Cofinite {
            excluded = held(excluded);
        }
    }

    /**
     * The strings a pattern admits, which are neither finitely many nor finitely many short of
     * everything.
     *
     * <p>A third shape because a format is a third kind of answer. {@code T[0-9]{13}} names ten
     * thousand billion strings and leaves out every other string there is, so neither of the two
     * above holds it — written as either, a reading would have to answer that the rule admits
     * everything, which is the answer that loses the rule.
     *
     * <p><b>Never empty and never everything.</b> Those two have their shapes already, and a second
     * spelling of either would be a set that {@link #isEmpty} and {@link #isAny} answer about by
     * asking which shape it is. {@link #matching} is where that is settled, and it is the only way
     * to one of these.
     *
     * <p>What the language holds is the whole of what this says. Two patterns accepting the same
     * strings are one set here, because a {@link souther.compiler.regex.Language} is its strings —
     * so a reading run twice over one model comes to values that are equal.
     *
     * <p><b>Over strings, as every set here is over one carrier.</b> {@link Cofinite} already means
     * every value of the carrier but these, so a set does not describe values of two kinds and never
     * did; what stands at a position is of the position's type. So a finite set met or joined with
     * one of these holds strings, and a value of another kind in it is a set belonging to no
     * position rather than a case for this to answer.
     */
    record Matching(souther.compiler.regex.Language language) implements ValueSet {

        public Matching {
            if (language == null) {
                throw new IllegalArgumentException("a pattern admits the strings of some language");
            }
        }
    }

    /**
     * The whole numbers in some runs, which comparisons of one number leave it.
     *
     * <p>A fourth shape because a choice between comparisons is a fourth kind of answer.
     * {@code r < 4 || r == 6} over a remainder by a thousand million leaves it a run of four numbers
     * and one more, and leaves out the run between, of nearly a thousand million: written as
     * {@link Finite} or {@link Cofinite} it is every one of them, and written as neither a reading
     * would have to answer that the comparisons admit everything. Held by the ends of its runs, what
     * it costs is how many comparisons made it ({@link WholeNumberRuns}).
     *
     * <p><b>Never empty, never everything, and never numbers apart or all numbers but some apart.</b>
     * Runs of one number each are a {@link Finite} of those numbers, and runs leaving out one number
     * at a time are a {@link Cofinite} of the numbers left out; {@link #wholeNumbers} is where that is
     * settled, and it is the only way to one of these.
     *
     * <p><b>One set, and sometimes two spellings of it.</b> A set of whole numbers some of which are
     * neighbours — {@code {1, 2}}, or every whole number but {@code 0} and {@code 1} — is a
     * {@link Finite} or a {@link Cofinite} where a rule named its values one by one, and one of these
     * where comparisons left it: counting runs out into values is the cost this shape is there to
     * avoid, so neither spelling is turned into the other. What is the same either way is every
     * question about the set — {@link #has}, {@link #sharesAnythingWith}, what it is met or joined
     * with ({@link Sets}) and whether it holds the same values as another
     * ({@link #holdsTheSameValuesAs}). {@code equals} is the spelling, and a reader asking whether
     * two sets are one set asks the last of those and not it.
     *
     * <p>Over the whole numbers, as every set here is over one carrier: a value that is no whole
     * number is in none of these.
     */
    record WholeRuns(WholeNumberRuns numbers) implements ValueSet {

        public WholeRuns {
            if (numbers == null || numbers.isNone() || numbers.isEvery()
                    || numbers.isNumbersApart() || numbers.others().isNumbersApart()) {
                throw new IllegalArgumentException(
                        "runs of whole numbers are no shape the others already hold: " + numbers);
            }
        }
    }

    /**
     * A set kept as it was given, and unable to be changed after.
     *
     * <p>The order is the order the model writes the values in, and it is kept because something
     * will be written out of one of these: a position admitting three cases of an enumeration is
     * three classes, and which order a reader lists them in is not a thing to leave to how a set
     * happened to store them. {@code Set.copyOf} is what this is not — its iteration order is
     * settled per run of the compiler, so the same model would list them one way today and another
     * way tomorrow.
     */
    private static Set<Value> held(Set<Value> values) {
        return Collections.unmodifiableSet(new LinkedHashSet<>(values));
    }

    /** Every value there is, which is what the rules leave where they say nothing. */
    ValueSet ANY = new Cofinite(Set.of());

    /** Nothing at all. */
    ValueSet NONE = new Finite(Set.of());

    /** Just this one value. */
    static ValueSet just(Value value) {
        return new Finite(Set.of(value));
    }

    /** Everything but this one value. */
    static ValueSet allBut(Value value) {
        return new Cofinite(Set.of(value));
    }

    /** These values and no others. */
    static ValueSet oneOf(Set<Value> values) {
        return new Finite(values);
    }

    /**
     * The strings {@code language} admits.
     *
     * <p>The one way to a {@link Matching}, and where a language that turns out to be one of the
     * two shapes already here becomes that shape. A pattern nothing satisfies is the empty set and
     * not a pattern with no strings; one that accepts everything is every value and not a pattern
     * that happens to leave nothing out. Held otherwise, {@link #isEmpty} would be a question about
     * which shape a set is written in, and the answer would turn on how a rule was spelled.
     *
     * <p>Reached through {@link Sets}, which has paid for the machine being asked those two
     * questions. What comes back from here is a set every later reader may observe for nothing.
     */
    static ValueSet matching(souther.compiler.regex.Language language) {
        if (language.isEmpty()) {
            return NONE;
        }
        if (language.isEverything()) {
            return ANY;
        }
        return new Matching(language);
    }

    /**
     * The whole numbers {@code numbers} holds.
     *
     * <p>The one way to a {@link WholeRuns}, and where runs that are one of the other shapes become
     * that shape: none and every number are {@link #NONE} and {@link #ANY}, numbers apart are the
     * {@link Finite} of them and every number but some apart is the {@link Cofinite} of those. Each
     * of the last two lists as many values as there are runs.
     */
    static ValueSet wholeNumbers(WholeNumberRuns numbers) {
        if (numbers.isNone()) {
            return NONE;
        }
        if (numbers.isEvery()) {
            return ANY;
        }
        if (numbers.isNumbersApart()) {
            return new Finite(numbersOf(numbers));
        }
        WholeNumberRuns left = numbers.others();
        if (left.isNumbersApart()) {
            return new Cofinite(numbersOf(left));
        }
        return new WholeRuns(numbers);
    }

    /** The one number of each run of {@code apart}, as values. */
    private static Set<Value> numbersOf(WholeNumberRuns apart) {
        Set<Value> out = new LinkedHashSet<>();
        apart.runs().forEach(run -> out.add(Value.number(new BigDecimal(run.from()))));
        return out;
    }

    /**
     * The whole number {@code value} is, or null where it is none: a number with nothing after the
     * point, which is what a run of whole numbers holds.
     */
    static BigInteger wholeNumberOf(Value value) {
        if (!(value instanceof Value.Number(BigDecimal number))) {
            return null;
        }
        ExactRatio exactly = ExactRatio.of(number);
        return exactly.isWhole() && exactly.floor() instanceof ExactAnswer.Held<BigInteger>(var whole)
                ? whole : null;
    }

    /**
     * Whether {@code value} is one of these.
     *
     * <p>Here, so that a reader wanting it does not answer it by asking which shape a set is. Every
     * shape has its own way of holding what it holds — one names them, one names what it leaves out,
     * one holds a language — and a caller reading that for itself is a second place the shapes are
     * enumerated, which the day a third arrived is exactly where it was not.
     */
    default boolean has(Value value) {
        return switch (this) {
            case Finite it -> it.values().contains(value);
            case Cofinite it -> !it.excluded().contains(value);
            // A language is a set of strings, so nothing that is not one is in it.
            case Matching it -> value instanceof Value.Text text && it.language().has(text.value());
            case WholeRuns it -> wholeNumberOf(value) instanceof BigInteger whole
                    && it.numbers().holds(whole);
        };
    }

    /**
     * Whether some value is in both, so far as that can be said without building anything.
     *
     * <p>A question a reader asks about a distinction it is deciding whether to keep, and not a
     * meet. What is wanted there is whether the position can still reach the case, and the set the
     * two come to is never looked at — so answering it by composing them would pay for a machine to
     * throw away, and would put a caller with no allowance in front of an operation that needs one.
     *
     * <p><b>One-sided where neither side can be counted out.</b> Two languages share a value only if
     * their product does, and that product is the expensive thing this exists to avoid. So the
     * answer there is that they may, which is what a reader with no proof does anyway: a case stays
     * unless something showed the position cannot reach it, and a case taken away on less than a
     * proof is a distinction the model states going missing.
     */
    default boolean sharesAnythingWith(ValueSet other) {
        if (this instanceof Finite it) {
            return it.values().stream().anyMatch(other::has);
        }
        if (other instanceof Finite) {
            return other.sharesAnythingWith(this);
        }
        // Runs against anything is what the two leave together, which is read off the ends and the
        // values written out and builds nothing.
        if (this instanceof WholeRuns || other instanceof WholeRuns) {
            return !Sets.metUnder(this, other, Meter.refusing()).isEmpty();
        }
        // Neither is finite, so each admits values without end and no finite thing either of them
        // holds out can be the whole of what the other has.
        return true;
    }

    /**
     * Whether this and {@code other} hold the same values, however each is spelled.
     *
     * <p>{@code equals} where neither is runs of whole numbers, since each set has one spelling
     * there. Where one is, the other is read as runs if it can be one — a set naming whole numbers,
     * or every value but some whole numbers — which is the values already written out put in order,
     * and the runs are never counted out. Runs hold whole numbers and nothing else, so a set naming
     * anything else, or a language, holds other values than they do.
     */
    default boolean holdsTheSameValuesAs(ValueSet other) {
        if (!(this instanceof WholeRuns) && !(other instanceof WholeRuns)) {
            return equals(other);
        }
        WholeNumberRuns mine = runsOf(this);
        return mine != null && mine.equals(runsOf(other));
    }

    /** The whole numbers {@code set} holds as runs, or null where it holds some other value or
     *  is no set of whole numbers runs can say. */
    private static WholeNumberRuns runsOf(ValueSet set) {
        return switch (set) {
            case WholeRuns it -> it.numbers();
            case Finite it -> wholeNumbersAmong(it.values());
            case Cofinite it -> {
                WholeNumberRuns excluded = wholeNumbersAmong(it.excluded());
                yield excluded == null ? null : excluded.others();
            }
            case Matching _ -> null;
        };
    }

    /** {@code values} as runs of one number each, or null where one of them is no whole number. */
    private static WholeNumberRuns wholeNumbersAmong(Set<Value> values) {
        List<BigInteger> numbers = new ArrayList<>();
        for (Value each : values) {
            BigInteger whole = wholeNumberOf(each);
            if (whole == null) {
                return null;
            }
            numbers.add(whole);
        }
        return WholeNumberRuns.of(numbers);
    }

    /** Whether no value is admitted, which is what refuses a declaration. */
    default boolean isEmpty() {
        return this instanceof Finite it && it.values().isEmpty();
    }

    /** Whether every value is admitted, so that nothing has been said. */
    default boolean isAny() {
        return this instanceof Cofinite it && it.excluded().isEmpty();
    }
}
