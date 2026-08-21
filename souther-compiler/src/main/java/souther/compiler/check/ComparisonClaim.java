package souther.compiler.check;

import souther.compiler.ast.Hir;

/**
 * What a comparison places on a position's values, read off the comparison and nothing else.
 *
 * <p>One classification, asked wherever a rule compares a position to something: a clause of an
 * invariant, a comparison in a body, a clause of an {@code ensures}. A rule is read the same way
 * wherever it is written (spec §boundary-coordinates), and this is the reading that says what it
 * placed. It was three: {@code InvariantBound.ordering} answered it for a {@code data}'s clauses,
 * {@code ComparedLine.of} for a body's and a declaration's comparisons, and
 * {@code GuardThresholds.orders} answered a coarser version of the same question under the same
 * word. Three answers to one question drift, and two of them already had: an equality places a line
 * where a body writes it and placed nothing where a {@code data} did.
 *
 * <p><b>Nothing about a carrier, a term, or a number here.</b> Whether the other side can be read as
 * a value of the position's order, and where the position sits in the value, are what a reading
 * answers about the comparison — and a question the model raises may not be decided by what a
 * reading managed (#851). So this takes an operator and gives what the model states, and a reader
 * that could not find the number still knows a line was placed.
 *
 * <p><b>And nothing about which values exist.</b> Whether there is anything on the far side of the
 * line is not the comparison's to say: an invariant refuses everything outside its bound at
 * construction, and a {@code guard} comparing the same number leaves values on both sides. That is a
 * fact about the construct the rule is written in, asked beside this rather than inside it — read as
 * one question, a guard's classification would carry an invariant's reason.
 */
public sealed interface ComparisonClaim {

    /**
     * An order: the values either side of the line are different classes.
     *
     * @param valueBelongsBelow whether the number named is on the low side. {@code x <= c} puts it
     *                          there; {@code x < c} puts it on the high side. Getting this wrong
     *                          moves the line by one and asks for a row that proves nothing
     * @param holdsAtTheValue   whether the comparison is true at the number named. Not derivable
     *                          from the other: {@code x <= c} and {@code x > c} agree about which
     *                          class the number is in and disagree here
     */
    record Cut(boolean valueBelongsBelow, boolean holdsAtTheValue) implements ComparisonClaim {}

    /**
     * A value singled out: the number named, and every other value as one class.
     *
     * <p>{@code x == c} and {@code x /= c} place the same thing. What they distinguish is the value
     * from every other value, and which of the two classes the comparison selects is
     * {@code holdsAtTheValue}, not a different partition — so reading either as a place to cut would
     * put an order between the two sides that the model never drew.
     *
     * <p>Which side is writable is the construct's answer and not this one. Under an invariant the
     * value singled out is admitted where the comparison holds at it and refused where it does not,
     * and a refused one leaves a hole rather than an edge: the values beside it are on both sides,
     * which is not what a boundary with a low side and a high side can carry.
     */
    record Singled(boolean holdsAtTheValue) implements ComparisonClaim {}

    /** Not a comparison of values at all, so nothing was placed. */
    record Nothing() implements ComparisonClaim {}

    /** What {@code op} places. */
    static ComparisonClaim of(Hir.BinOp op) {
        return switch (op) {
            case LE -> new Cut(true, true);
            case GT -> new Cut(true, false);
            case LT -> new Cut(false, false);
            case GE -> new Cut(false, true);
            case EQ -> new Singled(true);
            case NE -> new Singled(false);
            case AND, OR, ADD, SUB, MUL, DIV, CONCAT -> new Nothing();
        };
    }

    /** Whether {@code op} orders the values either side of what it names. */
    static boolean orders(Hir.BinOp op) {
        return of(op) instanceof Cut;
    }

    /** Whether {@code op} places anything at all, which is what a comparison does. */
    static boolean places(Hir.BinOp op) {
        return op.compares();
    }
}
