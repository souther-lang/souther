package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;

/**
 * The line a comparison between two positions draws: the place where the two hold one count.
 *
 * <p>{@link ComparedLine}'s sibling, and asked where that one came to nothing. A rule relating two
 * positions is not a partition of either (spec §what-a-position-admits), and that is an answer about
 * the classes rather than about the line — the row on the line is what tells a rule written
 * {@code >} from one written {@code >=}, and it is writable whenever the two positions have a count
 * they can both hold.
 *
 * <p>Read the same way whoever wrote the comparison. A {@code guard} and a comparison in an
 * {@code ensures} draw the same line between the same two positions; what differs is what meeting it
 * takes, and that is the origin's to answer rather than this one's.
 *
 * <p>Asked of the carrier and not of the type. Two operands compare only when they are of one type,
 * and a type is not what makes a line measurable: an enumeration's case is comparable on its sum's
 * order while carrying no places of its own, and two newtypes of one base are two types whose values
 * are ordered alike. What both sides can be read as is the carrier, so that is what is required to
 * be one.
 *
 * @param holdsAtTheLine whether the line's own values satisfy the comparison, which is what tells
 *                       {@code <} from {@code <=} and is the whole of what the row on the line shows
 */
record ComparedTerms(NumericTerm on, NumericTerm against, Carrier carrier,
                     boolean holdsAtTheLine) {

    /**
     * What {@code comparison} draws between two positions, or null where it draws no such line.
     *
     * <p>An equality is not one of these. {@code a == b} puts the whole of one arm on the line, and
     * that arm is already a row the branch measure asks for.
     */
    static ComparedTerms of(Core.Binary comparison, InputReads reads, Symbols symbols) {
        if (!ordersStrictly(comparison.op())) {
            return null;
        }
        NumericTerm on = GuardThresholds.termOf(comparison.left(), reads, symbols);
        NumericTerm against = GuardThresholds.termOf(comparison.right(), reads, symbols);
        if (on == null || against == null) {
            return null;   // a position inside an expression is not a place a row can be written at
        }
        Carrier carrier = Carrier.ofValue(comparison.left().type(), symbols);
        if (carrier == null
                || !carrier.equals(Carrier.ofValue(comparison.right().type(), symbols))) {
            return null;
        }
        return new ComparedTerms(on, against, carrier, holdsAtTheLine(comparison.op()));
    }

    /** Whether an operator orders its two sides, which {@code ==} and {@code /=} do not. */
    private static boolean ordersStrictly(Hir.BinOp op) {
        return switch (op) {
            case LT, LE, GT, GE -> true;
            case EQ, NE, AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
        };
    }

    private static boolean holdsAtTheLine(Hir.BinOp op) {
        return op == Hir.BinOp.LE || op == Hir.BinOp.GE;
    }
}
