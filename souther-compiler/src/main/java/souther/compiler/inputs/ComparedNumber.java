package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.core.Core;
import souther.compiler.numeric.Place;
import souther.compiler.types.BinOp;

/**
 * One comparison of a body, said as the number it is about and what it claims of that number.
 *
 * <p>The one reading of a comparison. Which number is compared, which side of it the comparison
 * keeps, and where the other side falls on that number's order are one answer and not three — a
 * reader that worked out any of them for itself would be reading the comparison a second time, and
 * two readings of one comparison are two answers as soon as they are asked under different bindings.
 *
 * <p><b>The place is on the number's order, and never on the position's.</b>
 * {@code Time.minute(slot.at) >= 30} names thirty on the order minutes are counted on; what stands
 * at {@code slot.at} is a time, and half past midnight is what that thirty would be there. The two
 * coincide only where the number is what the position holds.
 *
 * @param term   the number the comparison is about. A number over a run of values is one of these
 *               too: it is what the comparison is about, and it is answered by no single position
 * @param orders the order the number is written on and the one it is counted on, or null where
 *               nothing puts an order under it
 * @param claim  what the comparison says of the values either side of {@link #at}, with the operator
 *               turned round where the number was written on the right
 * @param at     where the other side falls on the number's order, or null where it is not a value
 *               that order writes — another position, a value this compiler does not place
 */
public record ComparedNumber(NumericTerm term, TermOrders orders, ComparisonClaim claim, Place at) {

    /**
     * What {@code comparison} says, or null where it names no number of this input at all.
     *
     * <p>The number-bearing side is read first and the comparison is turned round where the number
     * is on the right. What is answered here is layered: the number always, and the place and the
     * side only where the other operand is a value the number's order writes. A reader wanting a
     * line asks for one ({@link #drawsALine}); a reader wanting to know what the decision is about
     * takes the number and needs no more.
     */
    public static ComparedNumber of(Core.Binary comparison, InputReading read, InputReads reads) {
        // Whichever side draws a line, and the left where neither does and it names a number. A
        // number on the left that the right is not a value of is still the number the comparison
        // is about, unless the right is a number the left is a value of — then the line is on that
        // one, and the comparison is read turned round.
        ComparedNumber left = onOneSide(comparison.left(), comparison.right(), comparison.op(),
                read, reads);
        if (left != null && left.at() != null) {
            return left;
        }
        ComparedNumber right = onOneSide(comparison.right(), comparison.left(),
                mirrored(comparison.op()), read, reads);
        return right != null && right.at() != null ? right : left != null ? left : right;
    }

    /** The comparison read as being about a number {@code side} names, or null where it names none. */
    private static ComparedNumber onOneSide(Core side, Core other, BinOp op, InputReading read,
                                            InputReads reads) {
        Named named = namedBy(side, read, reads);
        if (named == null) {
            return null;
        }
        Carrier order = named.orders() == null ? null : named.orders().answered();
        return new ComparedNumber(named.term(), named.orders(), ComparisonClaim.of(op),
                order == null ? null : order.literalOf(other, read.symbols()));
    }

    /** The number this is about where one position answers it, and null where none does. */
    public NumericTerm.FromOnePosition atOnePosition() {
        return term.atOnePosition();
    }

    /**
     * Whether this says where a line falls: a number one position answers, on an order, cut at a
     * place of it.
     *
     * <p>The three together, because a line is all three. A comparison naming a number over a run
     * divides no position; one whose other side is another position states how far two of them
     * stand apart and is read elsewhere; one whose other side is a value the order does not write
     * is a rule this compiler did not read.
     */
    public boolean drawsALine() {
        return at != null && orders != null && atOnePosition() != null
                && !(claim instanceof ComparisonClaim.Nothing);
    }

    /** The number an expression names together with the orders it is read and counted on, or null
     *  where it names none. */
    private static Named namedBy(Core e, InputReading read, InputReads reads) {
        NumericTerm term = InputNumber.of(e, read.domain(), reads, read.symbols());
        if (term == null) {
            return null;
        }
        TermOrders orders = read.quantities().ordersOf(term);
        return new Named(term, orders == null || orders.answered() == null ? null : orders);
    }

    private record Named(NumericTerm term, TermOrders orders) { }

    private static BinOp mirrored(BinOp op) {
        return switch (op) {
            case LT -> BinOp.GT;
            case LE -> BinOp.GE;
            case GT -> BinOp.LT;
            case GE -> BinOp.LE;
            default -> op;
        };
    }
}
