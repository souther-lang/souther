package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.numeric.Place;
import souther.compiler.types.BinOp;

/**
 * One comparison of a body, said as the number it is about, the place it names on that number's
 * order, and what it claims either side of it.
 *
 * <p>The form every reader of a comparison works from. Which number is compared is
 * {@link InputNumber}'s answer, and where the other side falls is read on the order that number is
 * counted on — so a rule written {@code 100000 >= cost} and one written {@code cost <= 100000} come
 * to one value here, and a reader downstream never sees which side of the operator the number was
 * written on.
 *
 * <p><b>The place and not the operand.</b> {@code Time.minute(slot.at) >= 30} names thirty on the
 * order minutes are counted on, which is not the order the position is written on: what stands at
 * {@code slot.at} is a time. A reader taking the literal as written would hold a number belonging to
 * neither, and one taking it on the position's order would hold half past midnight.
 *
 * @param term    the number the comparison is about, answered by one position of the input
 * @param at      where the other side falls on that number's order
 * @param orders  the order the number is written on and the one it is counted on, which differ
 *                wherever the number is taken of what stands at the position
 * @param claim   what the comparison says of the values either side of {@link #at}, with the
 *                operator already turned round where the number was written on the right
 */
public record ComparedNumber(NumericTerm.FromOnePosition term, Place at, TermOrders orders,
                             ComparisonClaim claim) {

    /**
     * What {@code comparison} says, or null where it says nothing this reads.
     *
     * <p>The number-bearing side is read first and the comparison is turned round where the number
     * is on the right. Null where neither side names a number one position answers, or where the
     * other side is not a value that number's order writes — which is a rule this compiler did not
     * read rather than a rule the model does not state, and is reported as one where a report is
     * being made.
     */
    public static ComparedNumber asWritten(Core.Binary comparison, InputReads reads,
                                           Symbols symbols) {
        BinOp op = comparison.op();
        Named named = namedBy(comparison.left(), reads, symbols);
        Place at = named == null ? null : named.order().literalOf(comparison.right(), symbols);
        if (named == null || at == null) {
            named = namedBy(comparison.right(), reads, symbols);
            at = named == null ? null : named.order().literalOf(comparison.left(), symbols);
            op = mirrored(op);
        }
        NumericTerm.FromOnePosition term = named == null ? null : named.term().atOnePosition();
        if (term == null || at == null) {
            return null;
        }
        ComparisonClaim claim = ComparisonClaim.of(op);
        return claim instanceof ComparisonClaim.Nothing ? null
                : new ComparedNumber(term, at, named.orders(), claim);
    }

    /** The number an expression names together with the orders it is read and counted on, or null
     *  where it names none this can put an order under. */
    private static Named namedBy(Core e, InputReads reads, Symbols symbols) {
        NumericTerm term = InputNumber.of(e, reads, symbols);
        if (term == null) {
            return null;
        }
        TermOrders orders = reads.read().ordersOf(term, symbols);
        return orders.answered() == null ? null : new Named(term, orders);
    }

    private record Named(NumericTerm term, TermOrders orders) {

        Carrier order() {
            return orders.answered();
        }
    }

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
