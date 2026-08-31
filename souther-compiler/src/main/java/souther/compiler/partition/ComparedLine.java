package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.core.Core;
import souther.compiler.inputs.ComparedNumber;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermOrders;
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
 * @param value  where the line falls on the order the number is counted on, which is not the order
 *               the position is written on wherever the number is taken of what stands there: a
 *               line at thirty minutes past the hour is at thirty, and what the position holds is a
 *               time
 * @param orders both of those, so that a reader writing a row knows what to write there and a
 *               reader placing a line knows what it is placed against
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
record ComparedLine(NumericTerm.FromOnePosition term, Place value,
                    TermOrders orders,
                    boolean valueBelongsBelow, boolean holdsAtTheValue, boolean singles) {

    /**
     * What {@code comparison} draws, or null where it draws nothing.
     *
     * <p>Read once, by the reading every reader of a comparison shares
     * ({@link ComparedNumber}): which number is compared, which side of it
     * the comparison keeps, and where the other side falls on that number's order. What is left
     * here is turning that into a line.
     *
     * <p><b>The number's order and not the position's.</b> A count of a string's characters is
     * placed against whole numbers while what stands at the position is a string, and a rule on a
     * position holding dates is placed against a day count. The two are one order only where the
     * number is what the position holds — and a reading that took the position's order for both
     * wrote a minute of a time as a time.
     *
     * <p>Nothing here is a number against a value its order writes where that reading comes to
     * nothing, and there is nothing else for a spelling to try: which quantity a rule cuts is the
     * arithmetic's answer, and this reading is reached only where the arithmetic had none.
     */
    static ComparedLine asWritten(Core.Binary comparison,
                                  InputReading read, InputReads reads) {
        return of(ComparedNumber.of(comparison, read, reads));
    }

    /** The same comparison as a line, or null where it says nothing a line is drawn from. */
    private static ComparedLine of(ComparedNumber drawn) {
        if (drawn == null || !drawn.drawsALine()) {
            return null;
        }
        return switch (drawn.claim()) {
            case ComparisonClaim.Cut cut -> new ComparedLine(drawn.atOnePosition(), drawn.at(),
                    drawn.orders(), cut.valueBelongsBelow(), cut.holdsAtTheValue(), false);
            // A value singled out has no low side of its own — the values either side of it are one
            // class — so the side is written down as one answer and read by nobody.
            case ComparisonClaim.Singled singled -> new ComparedLine(drawn.atOnePosition(),
                    drawn.at(), drawn.orders(), true, singled.holdsAtTheValue(), true);
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
    static ComparedLine fromTheForm(AffineReading read,
                                    Quantities quantities) {
        if (read == null) {
            return null;
        }
        // The one position it cuts, where a single place answers that number. A quantity read from
        // somewhere else draws its line without dividing any position, and is a quantity of its own.
        NumericTerm coordinate = read.oneCoordinate();
        NumericTerm.FromOnePosition term =
                coordinate == null ? null : coordinate.atOnePosition();
        // The position's own order, not the order of whichever operand it was written beside. The
        // reading two methods up asks the same question of the same place, and `10 >= a + 1` names
        // the position on the right.
        TermOrders orders =
                term == null ? null : quantities.ordersOf(term);
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

}
