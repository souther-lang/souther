package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
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
record ComparedLine(NumericTerm term, Place value, boolean valueBelongsBelow,
                    boolean holdsAtTheValue, boolean singles) {

    /**
     * What {@code comparison} draws, or null where it draws nothing.
     *
     * <p>The position-bearing side is read first and the comparison is turned round where it is on
     * the right: {@code 100000 >= cost} says what {@code cost <= 100000} says. The carrier comes
     * from the side that named the position, so the literal on the other side is read on the carrier
     * the line is being drawn on — a size call is an {@code Int} there, and a position holding dates
     * is a day count.
     */
    static ComparedLine of(Core.Binary comparison, InputReads reads, Symbols symbols) {
        Hir.BinOp op = comparison.op();
        NumericTerm term = GuardThresholds.termOf(comparison.left(), reads, symbols);
        Place value = Carrier.writtenOn(comparison.right(), comparison.left().type(), symbols);
        if (term == null || value == null) {
            term = GuardThresholds.termOf(comparison.right(), reads, symbols);
            value = Carrier.writtenOn(comparison.left(), comparison.right().type(), symbols);
            op = mirrored(op);
        }
        if (term == null || value == null) {
            return null;
        }
        Boolean below = switch (op) {
            case LE, GT -> Boolean.TRUE;    // the value itself is on the low side
            case LT, GE -> Boolean.FALSE;   // and here it is on the high side
            default -> null;                // EQ / NE do not order the values, so they cut nothing
        };
        if (below == null) {
            // An equality singles the value out instead. Recorded as that rather than as a place to
            // cut, because the values either side of it are not a distinction the model has drawn.
            return op == Hir.BinOp.EQ || op == Hir.BinOp.NE
                    ? new ComparedLine(term, value, true, op == Hir.BinOp.EQ, true) : null;
        }
        // True at the line's own value for the operators that include it, which is not the same
        // question as which class the value falls in: `x <= c` and `x > c` agree about the second.
        return new ComparedLine(term, value, below, op == Hir.BinOp.LE || op == Hir.BinOp.GE, false);
    }

    private static Hir.BinOp mirrored(Hir.BinOp op) {
        return switch (op) {
            case LT -> Hir.BinOp.GT;
            case LE -> Hir.BinOp.GE;
            case GT -> Hir.BinOp.LT;
            case GE -> Hir.BinOp.LE;
            default -> op;
        };
    }
}
