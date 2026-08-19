package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
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
 * @param valueBelongsBelow which side of the line the pair standing on it belongs to. Not derivable
 *                       from {@link #holdsAtTheLine}, which says what happens on the line and
 *                       nothing about either side of it: {@code a < b} and {@code a > b} agree there
 *                       and are opposite everywhere else. Together the two say which way the rule is
 *                       satisfied, which is what a border is read off
 * @param stepsApart     how far apart the rule holds them, in the carrier's own steps. Zero where
 *                       the rule cuts where they meet, which is every comparison written as one
 *                       position against another
 */
record ComparedTerms(NumericTerm on, NumericTerm against, Carrier carrier,
                     boolean holdsAtTheLine, boolean valueBelongsBelow, long stepsApart) {

    /**
     * Which side of the line the pair standing on it belongs to.
     *
     * <p>Derived rather than written down, and derived here so that a border reads it the same way
     * whatever it was drawn on. What a border needs is which way the rule is satisfied, and that
     * follows from this together with whether the rule holds on the line — the pair every rule
     * records about its own threshold. Recorded as a third fact it would be free to disagree with
     * them, and a line whose sides were the wrong way round asks for two rows that prove nothing.
     */
    /**
     * What {@code comparison} draws between two positions, or null where it draws no such line.
     *
     * <p>An equality is not one of these. {@code a == b} puts the whole of one arm on the line, and
     * that arm is already a row the branch measure asks for.
     */
    static ComparedTerms of(Core.Binary comparison, InputReads reads, Symbols symbols) {
        Carrier carrier = Carrier.ofValue(comparison.left().type(), symbols);
        if (carrier == null || !carrier.equals(Carrier.ofValue(comparison.right().type(), symbols))) {
            return null;
        }
        if (ordersStrictly(comparison.op())) {
            NumericTerm on = GuardThresholds.termOf(comparison.left(), reads, symbols);
            NumericTerm against = GuardThresholds.termOf(comparison.right(), reads, symbols);
            if (on != null && against != null) {
                return new ComparedTerms(on, against, carrier, holdsAtTheLine(comparison.op()),
                        holdsAtTheLine(comparison.op()) == !onIsAbove(comparison.op()), 0);
            }
        }
        return fromTheForm(comparison, carrier, reads, symbols);
    }

    /**
     * The distance the canonical form holds two positions apart, where it holds two apart.
     *
     * <p>Coefficients of one and minus one and nothing else, because that is what makes the quantity
     * a distance: {@code 2a - b} is not how far two positions stand apart, it is an arithmetic form
     * over both of them, and its border is a border of that form.
     *
     * <p>The threshold need not be zero. {@code a < b - 1} holds the two at least two apart, and
     * where they meet is not where that rule cuts — read as a line at zero it would ask for a pair
     * that proves nothing about it.
     */
    private static ComparedTerms fromTheForm(Core.Binary comparison, Carrier carrier,
                                             InputReads reads, Symbols symbols) {
        AffineReading read = AffineReading.of(comparison, reads, symbols);
        if (read == null || !read.orders()) {
            return null;
        }
        NumericTerm[] two = read.twoCoordinates();
        if (two == null) {
            read = read.mirrored();
            two = read.twoCoordinates();
        }
        if (two == null || !carrier.counts()) {
            return null;
        }
        ComparisonClaim.Cut cut = (ComparisonClaim.Cut) read.claim();
        return new ComparedTerms(two[0], two[1], carrier, cut.holdsAtTheValue(),
                cut.valueBelongsBelow(), read.cut().longValueExact());
    }

    /** Which side the left of the comparison is on where the comparison is satisfied. Read off the
     *  operator as written, since neither side is turned round here. */
    private static boolean onIsAbove(Hir.BinOp op) {
        return op == Hir.BinOp.GT || op == Hir.BinOp.GE;
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
