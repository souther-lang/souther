package souther.compiler.check;

import souther.compiler.numeric.Towards;
import souther.compiler.types.BinOp;

/**
 * What an operator places on a position's values, asked of any operator the language writes.
 *
 * <p>The wide answer, and the one place the two vocabularies meet. An operator either compares two
 * values or does not, and only the first kind places anything: {@code &&} joins comparisons and
 * {@code +} answers a number, and neither divides a position. So this has an arm for an operator
 * that places nothing, and {@link ComparisonClaim} — what a comparison placed — has none.
 *
 * <p><b>Asked once, and carried as what it answered.</b> Whoever establishes that an operator
 * compares holds the claim from that moment, rather than a {@code boolean} saying it does: a reader
 * handed the {@code boolean} still holds an operator, and reading the operator again below the
 * point where the question was settled leaves every consumer answering for a case that was already
 * excluded. What such an answer says is invented, and nothing observes it until the day something
 * does.
 *
 * <p><b>Nothing about a carrier, a term, or a number here.</b> Whether the other side can be read as
 * a value of the position's order, and where the position sits in the value, are what a reading
 * answers about the comparison. So this takes an operator and gives what the model states, and a
 * reader that could not find the number still knows a line was placed.
 */
public sealed interface ComparisonPlacement permits ComparisonClaim, ComparisonPlacement.Nothing {

    /**
     * The same placement, read with the comparison's two sides written the other way round.
     *
     * <p>The meaning of the swap and not the swap itself. A reader that has one side on the left
     * and wants the other there turns the statement round once, here, rather than making the
     * operator it would have been written with and asking what that one places — two ways from an
     * operator to a meaning, and the second is a table of operators standing beside this one.
     */
    ComparisonPlacement turned();

    /** Not a comparison of values at all, so nothing was placed. */
    record Nothing() implements ComparisonPlacement {

        @Override
        public ComparisonPlacement turned() {
            return this;
        }
    }

    /**
     * What {@code op} places, which is nothing where it is not a comparison.
     *
     * <p>Which operators compare is {@link BinOp#compares}'s answer and this asks it rather
     * than listing them again. Two lists can be given different answers about one operator added
     * later, and they fail in opposite directions: the numbering would leave it out of the
     * comparisons of a body while this said what it cuts, so a line would be drawn on a comparison
     * no run records and no row could ever meet it.
     */
    static ComparisonPlacement of(BinOp op) {
        if (!op.compares()) {
            return new Nothing();
        }
        return switch (op) {
            case LE -> new ComparisonClaim.Cut(Towards.BELOW, true);
            case GT -> new ComparisonClaim.Cut(Towards.BELOW, false);
            case LT -> new ComparisonClaim.Cut(Towards.ABOVE, false);
            case GE -> new ComparisonClaim.Cut(Towards.ABOVE, true);
            case EQ -> new ComparisonClaim.Singled(true);
            case NE -> new ComparisonClaim.Singled(false);
            // Refused above and written out here so the switch stays exhaustive: an operator added
            // to the language stops the compile here and is decided about rather than falling in.
            case AND, OR, ADD, SUB, MUL, DIV, CONCAT -> new Nothing();
        };
    }

}
