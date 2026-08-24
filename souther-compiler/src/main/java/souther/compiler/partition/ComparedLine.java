package souther.compiler.partition;

import souther.compiler.types.BinOp;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

/**
 * What one comparison says about a position, whoever wrote the comparison.
 *
 * <p>Which number a line can be drawn on, where it falls, and which side of it the value itself is
 * on are the same questions of a {@code guard} and of a comparison in an {@code ensures} — a rule is
 * read the same way wherever it is written (spec §boundary-coordinates). What differs is what
 * meeting the line takes, and that is the origin's to say rather than this one's.
 *
 * <p>The construction and not the entry. Each reader finds its own comparisons — one walks the
 * conditions of a body, the other the rules of a declaration — and the two have nothing to say to
 * each other about where to look.
 *
 * @param valueBelongsBelow whether {@code value} itself is on the low side. {@code x <= c} puts it
 *                          there; {@code x < c} puts it on the high side. Getting this wrong moves
 *                          the boundary by one and asks for a row that proves nothing
 * @param holdsAtTheValue   whether the comparison is true at the line's own value. Not derivable
 *                          from {@code valueBelongsBelow}: {@code x <= c} and {@code x > c} agree
 *                          about the class the value is in and disagree here
 * @param singles           whether the comparison singles the value out rather than ordering the
 *                          values either side of it. An equality says nothing about ranges: what it
 *                          distinguishes is the value from every other value
 */
record ComparedLine(NumericTerm term, Place value, souther.compiler.inputs.TermOrders orders,
                    boolean valueBelongsBelow, boolean holdsAtTheValue, boolean singles) {

    /**
     * What {@code comparison} draws, or null where it draws nothing.
     *
     * <p>The position-bearing side is read first and the comparison is turned round where it is on
     * the right: {@code 100000 >= cost} says what {@code cost <= 100000} says. The carrier is the
     * position's own ({@link souther.compiler.inputs.InputDomain#carrierOf}), and the literal on the
     * other side is read on it — a size call is an {@code Int} there, and a position holding dates
     * is a day count.
     *
     * <p>The position's order and not the operand's type, which is a distinction that costs nothing
     * here and everything next door. An operand that names a position is written as that position,
     * so the two agreed wherever this reading reached an answer at all; the reading beside this one
     * compares what an operation answered, and there the operands are whole numbers while the
     * positions hold dates (#1018). One question with one place to ask it is what keeps that from
     * depending on which reading a rule happens to fall into.
     */
    static ComparedLine of(Core.Binary comparison, AffineReading read, InputReads reads,
                           Symbols symbols) {
        BinOp op = comparison.op();
        GuardThresholds.Named named = GuardThresholds.namedBy(comparison.left(), reads, symbols);
        Place value = named == null ? null : named.order().literalOf(comparison.right(), symbols);
        if (named == null || value == null) {
            named = GuardThresholds.namedBy(comparison.right(), reads, symbols);
            value = named == null ? null : named.order().literalOf(comparison.left(), symbols);
            op = mirrored(op);
        }
        NumericTerm term = named == null ? null : named.term();
        souther.compiler.inputs.TermOrders orders = named == null ? null : named.orders();
        if (term == null || value == null) {
            // Nothing here is a position against a value the carrier writes. It may still be a
            // statement about one position: `a + 1 <= 10` and `a <= b - b + 9` are both `a <= 9`,
            // and which quantity a rule cuts is the arithmetic's answer rather than the spelling's.
            return fromTheForm(read, reads, symbols);
        }
        return switch (ComparisonClaim.of(op)) {
            case ComparisonClaim.Cut cut -> new ComparedLine(term, value, orders,
                    cut.valueBelongsBelow(), cut.holdsAtTheValue(), false);
            // A value singled out has no low side of its own — the values either side of it are one
            // class — so the side is written down as one answer and read by nobody.
            case ComparisonClaim.Singled singled ->
                    new ComparedLine(term, value, orders, true, singled.holdsAtTheValue(), true);
            case ComparisonClaim.Nothing _ -> null;
        };
    }

    /**
     * The line the canonical form draws where it cuts one position with a coefficient of one.
     *
     * <p>A coefficient of one and no other, because that is what makes the quantity the position's
     * own values. {@code 2 * a <= 9} cuts something that is not {@code a}: it takes the even numbers,
     * nine is not one of them, and reading it as a line on {@code a} would put a row at four and a
     * half. That is a quantity of its own ({@link BorderQuantity.OverAForm}) and is read elsewhere.
     */
    private static ComparedLine fromTheForm(AffineReading read, InputReads reads,
                                            Symbols symbols) {
        if (read == null) {
            return null;
        }
        NumericTerm term = read.oneCoordinate();
        // The position's own order, not the order of whichever operand it was written beside. The
        // reading two methods up asks the same question of the same place, and `10 >= a + 1` names
        // the position on the right.
        souther.compiler.inputs.TermOrders orders =
                term == null ? null : reads.read().ordersOf(term, symbols);
        if (orders == null || orders.answered() == null || !orders.answered().counts()) {
            return null;
        }
        Carrier carrier = orders.answered();
        Place value = Count.of(read.cut());
        return switch (read.claim()) {
            case ComparisonClaim.Cut cut -> new ComparedLine(term, value, orders,
                    cut.valueBelongsBelow(), cut.holdsAtTheValue(), false);
            case ComparisonClaim.Singled singled ->
                    new ComparedLine(term, value, orders, true, singled.holdsAtTheValue(), true);
            case ComparisonClaim.Nothing _ -> null;
        };
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
