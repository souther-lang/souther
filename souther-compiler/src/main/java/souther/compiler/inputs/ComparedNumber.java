package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.ComparisonPlacement;
import souther.compiler.core.Core;
import souther.compiler.numeric.Place;

/**
 * One binary of a body, said as the number it is about and what its operator places on that number.
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
 * @param placed what the comparison says of the values either side of {@link #at}, turned round
 *               where the number was written on the right. The wide classification, because what
 *               reaches this reading is any binary a walk met: an arithmetic operator names numbers
 *               too and places nothing on them
 * @param at     where the other side falls on the number's order, or null where it is not a value
 *               that order writes — another position, a value this compiler does not place
 */
public record ComparedNumber(NumericTerm term, TermOrders orders, ComparisonPlacement placed,
                             Place at) {

    /**
     * What one comparison of a body draws: the number, where the line falls on it, and what the
     * rule placed there.
     *
     * <p>Everything a line is, in one value, made where all of it is known. A reader handed the
     * reading and a {@code boolean} saying it draws a line still holds the parts that may be absent
     * and the classification of an operator that places nothing, and has to take them apart again —
     * so this is what such a reader is handed instead, and there is no state of it in which a line
     * is missing a part of itself.
     *
     * @param term   the position the line is on
     * @param at     where on its order the line falls
     * @param orders the order it is read and written back on
     * @param claim  what the rule placed there
     */
    public record DrawnLine(NumericTerm.FromOnePosition term, Place at, TermOrders orders,
                            ComparisonClaim claim) {}

    /**
     * What {@code binary} says, or null where it names no number of this input at all.
     *
     * <p>The number-bearing side is read first and the comparison is turned round where the number
     * is on the right. What is answered here is layered: the number always, and the place and the
     * side only where the other operand is a value the number's order writes. A reader wanting a
     * line asks for one ({@link #line}); a reader wanting to know what the decision is about takes
     * the number and needs no more.
     */
    public static ComparedNumber of(Core.Binary binary, InputReading read, InputReads reads) {
        ComparisonPlacement placed = ComparisonPlacement.of(binary.op());
        // Whichever side draws a line, and the left where neither does and it names a number. A
        // number on the left that the right is not a value of is still the number the comparison
        // is about, unless the right is a number the left is a value of — then the line is on that
        // one, and the comparison is read turned round.
        ComparedNumber left = onOneSide(binary.left(), binary.right(), placed, read, reads);
        if (left != null && left.at() != null) {
            return left;
        }
        // Turned round as what it states and not as the operator it would have been written with:
        // which side a number stands on is how the source was spelled, and what the rule places is
        // read off the operator once.
        ComparedNumber right =
                onOneSide(binary.right(), binary.left(), placed.turned(), read, reads);
        return right != null && right.at() != null ? right : left != null ? left : right;
    }

    /** The comparison read as being about a number {@code side} names, or null where it names none. */
    private static ComparedNumber onOneSide(Core side, Core other, ComparisonPlacement placed,
                                            InputReading read, InputReads reads) {
        Named named = namedBy(side, read, reads);
        if (named == null) {
            return null;
        }
        Carrier order = named.orders() == null ? null : named.orders().answered();
        return new ComparedNumber(named.term(), named.orders(), placed,
                order == null ? null : order.literalOf(other, read.symbols()));
    }

    /** The number this is about where one position answers it, and null where none does. */
    public NumericTerm.FromOnePosition atOnePosition() {
        return term.atOnePosition();
    }

    /**
     * Where this says a line falls, or null where it says no line falls anywhere.
     *
     * <p>All of it together, because a line is all of it. A comparison naming a number over a run
     * divides no position; one whose other side is another position states how far two of them
     * stand apart and is read elsewhere; one whose other side is a value the order does not write
     * is a rule this compiler did not read; and an operator that placed nothing drew nothing.
     *
     * <p><b>The one narrowing, and it hands over what it established.</b> This is where a reading
     * of any binary a walk met becomes a line, so it is where an operator that places nothing stops
     * — and every reader below takes {@link DrawnLine}, which has no case for one.
     */
    public DrawnLine line() {
        NumericTerm.FromOnePosition position = atOnePosition();
        if (at == null || orders == null || position == null) {
            return null;
        }
        return placed instanceof ComparisonClaim claim
                ? new DrawnLine(position, at, orders, claim) : null;
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
}
