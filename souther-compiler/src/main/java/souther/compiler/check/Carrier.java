package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.DateTimes;
import souther.compiler.numeric.Granularity;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

/**
 * What a position's counts stand for, and the only place either direction is crossed.
 *
 * <p>The interval algebra holds one number per position, so a type takes part in it by having an
 * order-preserving count and a way back. Whether a type has one is this question, asked here and
 * nowhere else: it was answered in three places that disagreed — a predicate deciding what a report
 * said, a reader deciding what an invariant bounded, and a table deciding how a value was written
 * back — so a {@code Date} was a carrier to one of them and not to another, and the disagreement
 * showed up as a bound that vanished without a word.
 *
 * <p><b>Closed both ways.</b> Everything that turns a value into a {@link Count} and everything that
 * turns a {@link Count} back into a value is a method here. Outside this type nothing may read a
 * count as a number a model wrote, or build a value out of one: those were the leaks, and each of
 * them was a reader that had a carrier available and did not ask it. A reader that sniffed a written
 * temporal for a {@code T} to decide whether it was counting days or seconds is the shape they all
 * had — the declared type says which, and guessing from the text is a second answer to a question
 * already answered.
 *
 * <p><b>Exhaustive over {@link Type.Prim}.</b> A primitive added to the language stops the build
 * here, at the one place that would otherwise answer for it by omission. What this does not close is
 * the rest of the ordered types (spec §primitives): a single-value newtype is reduced to its base
 * before this is asked, and an enumeration is ordered by its declaration and is not a primitive at
 * all.
 */
public enum Carrier {

    /** A whole number: an {@code Int}, and every size. */
    WHOLE,

    /** A decimal. */
    DENSE,

    /** A day count, standing for a date. */
    DATE,

    /** A second count, standing for a date-time. Apart from {@link #DATE}: two units in one carrier
     *  would leave a line drawn on a day beside one drawn on a second with nothing saying which. */
    MOMENT;

    /**
     * The carrier a location's own content is counted on, or null where nothing here draws a line on
     * it.
     *
     * <p>Asked of what the names wrap, so a newtype answers as the value it carries — which is what
     * makes {@code data Cutoff = Date} the same carrier as a bare {@code Date}.
     */
    public static Carrier ofValue(Type type, Symbols symbols) {
        if (!(TypeOps.base(type, symbols) instanceof Type.Prim prim)) {
            return null;
        }
        return switch (prim) {
            case INT -> WHOLE;
            case DECIMAL -> DENSE;
            case DATE -> DATE;
            case DATETIME -> MOMENT;
            // `String` is ordered and has no count to embed into, so nothing here draws a line on
            // it. `Bool` and `Raw` are not ordered at all.
            case STRING, BOOL, RAW -> null;
        };
    }

    /** How the counts on this carrier are spaced, which is what decides whether a strict bound has a
     * next count to step to. */
    public Granularity spacing() {
        return switch (this) {
            case WHOLE, DATE -> Granularity.DISCRETE;
            // No smallest step this language names. A strict bound then leaves its end on the count
            // it names and says that count is not one of its own, rather than inventing a step in.
            case DENSE, MOMENT -> Granularity.DENSE;
        };
    }

    /**
     * The count as this carrier can actually hold it, or null where it holds nothing there.
     *
     * <p>Not every number between two of this carrier's counts is one of them. A date-time is dense
     * in the sense that matters to a strict bound — there is no step to sharpen one onto — and the
     * counts it can be written as still sit on a grid, at the nanosecond. Halfway between two
     * adjacent ones is a number and not a date-time.
     *
     * <p>Asked wherever a count is about to stand for a value. Left unasked, a class open at both
     * ends between two adjacent moments offered the count between them, which was written back as one
     * of the ends — a row labelled for a class it is not in.
     */
    public Count onTheGrid(Count count) {
        if (count == null) {
            return null;
        }
        return switch (this) {
            // A decimal holds every number: the ranges and the values are the same numbers.
            case DENSE -> count;
            // A whole number and a day count step, so a number between two of them is neither, and
            // each stops where what carries it stops. Asked here rather than at each place that
            // steps one, because a step off the end is the same non-value however it was reached.
            case WHOLE -> count.whole() && within(count, Long.MIN_VALUE, Long.MAX_VALUE)
                    ? count : null;
            case DATE -> count.whole()
                    && within(count, java.time.LocalDate.MIN.toEpochDay(),
                            java.time.LocalDate.MAX.toEpochDay())
                    ? count : null;
            case MOMENT -> DateTimes.secondOf(DateTimes.written(count));
        };
    }

    private static boolean within(Count count, long low, long high) {
        return count.at().compareTo(java.math.BigDecimal.valueOf(low)) >= 0
                && count.at().compareTo(java.math.BigDecimal.valueOf(high)) <= 0;
    }

    /**
     * The count a rule's literal names on this carrier, or null where the expression names none.
     *
     * <p>Which literals a rule may be bounded by is a fact about what carries the value and not about
     * the reader that wants one, so it is answered here. It was being answered separately by each
     * reader instead, and an invariant and a {@code guard} at one position admitted different rules
     * with only one of them saying so.
     */
    public Count literalOf(Ast.Expr e) {
        return switch (this) {
            case WHOLE -> Count.of(InvariantBound.wholeLiteral(e));
            case DENSE -> Count.of(InvariantBound.literalOf(e));
            case DATE -> temporal(e, "Date", Dates::dayOf);
            case MOMENT -> temporal(e, "DateTime", DateTimes::secondOf);
        };
    }

    /** The count a written temporal is, or null where the expression is not one of that kind. A
     *  temporal is written as a literal with its text spelled out (spec
     *  §a-temporal-value-is-written-as-a-literal), so it is read here rather than run. */
    private static Count temporal(Ast.Expr e, String written,
                                  java.util.function.Function<String, Count> countOf) {
        return e instanceof Ast.Apply call && written.equals(call.reaches())
                && call.args().size() == 1 && call.args().get(0) instanceof Ast.StringLit iso
                ? countOf.apply(iso.value()) : null;
    }

    /**
     * The count an observed value is on this carrier, or null where the value is not one of this
     * carrier's.
     *
     * <p>Null is about the value and not about this: a {@code Text} where a date was expected is a
     * value the position does not hold, and a caller with a reason to keep is the one that has it.
     *
     * <p>A newtype is not a step in a path, so what sits at a position may be the construction with
     * the value one inside it. Reached through rather than refused, which is how a wrapped number and
     * a bare one are the same count.
     */
    public Count countOf(ObservedValue value) {
        ObservedValue at = value instanceof ObservedValue.Constructed c && c.field("value") != null
                ? c.field("value") : value;
        return switch (this) {
            // A whole number written as a decimal is the same count; whether the position admits a
            // fraction is the range's question and not this one's.
            case WHOLE, DENSE -> switch (at) {
                case ObservedValue.Integer i -> Count.of(i.value());
                case ObservedValue.Decimal d -> Count.of(d.value());
                case null, default -> null;
            };
            case DATE -> at instanceof ObservedValue.Temporal t ? Dates.dayOf(t.iso()) : null;
            case MOMENT -> at instanceof ObservedValue.Temporal t ? DateTimes.secondOf(t.iso()) : null;
        };
    }

    /**
     * The value a count stands for, as an observation of it would look.
     *
     * <p>The one place a count leaves the algebra. A date is a day count inside the ranges and a date
     * everywhere a person reads it, and the conversion sitting here is what keeps a cut, a report and
     * a fixture from disagreeing about which of the two a line is drawn at.
     */
    public ObservedValue valueOf(Count count) {
        return switch (this) {
            case WHOLE -> new ObservedValue.Integer(count.at().longValueExact());
            case DENSE -> new ObservedValue.Decimal(count.at());
            case DATE -> new ObservedValue.Temporal(Dates.written(count));
            case MOMENT -> new ObservedValue.Temporal(DateTimes.written(count));
        };
    }

    /**
     * A count as an author would write the value it stands for. A report that printed the count
     * itself would name a line at a number nobody wrote.
     *
     * <p>The number and not how many places it was written to, which is the same thing that makes
     * two cuts one cut ({@link Count#key()}). A line an invariant and a {@code guard} both draw is
     * one line recorded once, and the spelling it keeps is whichever rule reached it first — so a
     * label that preserved places would print one line two ways depending on the order the rules
     * were read in.
     */
    public String written(Count count) {
        return switch (this) {
            case WHOLE, DENSE -> count.key();
            case DATE -> Dates.written(count);
            case MOMENT -> DateTimes.written(count);
        };
    }
}
