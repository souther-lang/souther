package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.numeric.Granularity;
import souther.compiler.types.Type;

/**
 * What a term's numbers stand for, and which values have one at all.
 *
 * <p>The interval algebra holds one number, so a type takes part in it by having an order-preserving
 * count and a way back. Whether a type has one is this question, asked here and nowhere else: it was
 * answered in three places that disagreed — a predicate deciding what a report said, a reader
 * deciding what an invariant bounded, and a table deciding how a value was written back — so a
 * {@code Date} was a carrier to one of them and not to another, and the disagreement showed up as a
 * bound that vanished without a word.
 *
 * <p><b>Exhaustive over {@link Type.Prim}.</b> A primitive added to the language stops the build
 * here, at the one place that would otherwise answer for it by omission. What this does not close is
 * the rest of the ordered types (spec §primitives): a single-value newtype is reduced to its base
 * before this is asked, and an enumeration is ordered by its declaration and is not a primitive at
 * all, so neither is guarded by the switch below and both are recognised by their own readers.
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
     * The carrier a location's own content is read on, or null where nothing here draws a line on it.
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

    /**
     * The carrier a term's numbers are on, or null where it has none.
     *
     * <p>A size is a whole number whatever it is a size of, so the term answers this and not the
     * position: a rule about the length of a string is carried as an {@code Int} at a position no
     * line is drawn on.
     */
    public static Carrier of(NumericTerm term, Type positionType, Symbols symbols) {
        return term instanceof NumericTerm.SizeOf ? WHOLE : ofValue(positionType, symbols);
    }

    /** How the values on this carrier are spaced, which is what decides whether a strict bound has a
     * next value to step to. */
    public Granularity spacing() {
        return switch (this) {
            case WHOLE, DATE -> Granularity.DISCRETE;
            // No smallest step this language names. A strict bound then leaves its end on the value
            // it names and says that value is not one of its own, rather than inventing a step in.
            case DENSE, MOMENT -> Granularity.DENSE;
        };
    }

    /**
     * The count as this carrier can actually hold it, or null where it holds nothing there.
     *
     * <p>Not every number between two of this carrier's values is one of them. A date-time is dense
     * in the sense that matters to a strict bound — there is no step to sharpen one onto — and the
     * values it can be written as still sit on a grid, at the nanosecond. Halfway between two
     * adjacent ones is a number and not a date-time.
     *
     * <p>Asked wherever a count is about to stand for a value. Left unasked, a class open at both
     * ends between two adjacent moments offered the number between them, which was written back as
     * one of the ends — a row labelled for a class it is not in.
     */
    public java.math.BigDecimal onTheGrid(java.math.BigDecimal count) {
        return switch (this) {
            // A whole number, a decimal and a day count are held as they are: the ranges and the
            // values are the same numbers.
            case WHOLE, DENSE, DATE -> count;
            case MOMENT -> DateTimes.secondOf(DateTimes.written(count));
        };
    }

    /** How the values beside a boundary on this carrier are found. */
    public BoundaryDomain intervals() {
        return switch (this) {
            case WHOLE -> BoundaryDomain.INT;
            case DENSE -> BoundaryDomain.DECIMAL;
            case DATE -> BoundaryDomain.DATE;
            case MOMENT -> BoundaryDomain.MOMENT;
        };
    }
}
