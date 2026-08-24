package souther.compiler.partition;

import souther.compiler.types.BinOp;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;

import java.util.LinkedHashMap;
import java.util.Map;

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
 * are ordered alike. What both sides can be read as is the carrier, so that is what is asked about.
 *
 * <p><b>Of the positions' carriers, and never of the operands'.</b> The two agree wherever a rule
 * names its positions itself, and part company the moment an operation stands between them: the
 * operands of {@code Date.daysBetween(a, b) > 10} are whole numbers and its positions hold dates.
 * Read off the comparison, both positions were written back and read off a row as whole numbers, and
 * the border could be met by no row and composed for by none (#1018).
 *
 * @param holdsAtTheLine whether the line's own values satisfy the comparison, which is what tells
 *                       {@code <} from {@code <=} and is the whole of what the row on the line shows
 * @param valueBelongsBelow which side of the line the pair standing on it belongs to. Not derivable
 *                       from {@link #holdsAtTheLine}, which says what happens on the line and
 *                       nothing about either side of it: {@code a < b} and {@code a > b} agree there
 *                       and are opposite everywhere else. Together the two say which way the rule is
 *                       satisfied, which is what a border is read off
 * @param stepsApart     how far apart the rule holds them, as a number on the carrier's counts.
 *                       Zero where the rule cuts where they meet, which is every comparison written
 *                       as one position against another. A number and not a count of steps: an order
 *                       with no smallest step still holds its values a distance apart
 */
record ComparedTerms(NumericTerm on, NumericTerm against, Map<NumericTerm, Carrier> carriers,
                     boolean holdsAtTheLine, boolean valueBelongsBelow, Count stepsApart) {

    /**
     * What {@code comparison} draws between two positions, or null where it draws no such line.
     *
     * <p>An equality is not one of these. {@code a == b} puts the whole of one arm on the line, and
     * that arm is already a row the branch measure asks for.
     */
    static ComparedTerms of(Core.Binary comparison, AffineReading read, InputReads reads,
                            Symbols symbols) {
        if (ordersStrictly(comparison.op())) {
            GuardThresholds.Named on = GuardThresholds.namedBy(comparison.left(), reads, symbols);
            GuardThresholds.Named against =
                    GuardThresholds.namedBy(comparison.right(), reads, symbols);
            Map<NumericTerm, Carrier> carriers = on == null || against == null ? null
                    : aDistanceBetween(on.term(), on.on(), against.term(), against.on());
            if (carriers != null) {
                // The subject is the one the author wrote on the left, which the canonical form
                // keeps too. Which of the two a line is named by is not something to derive where
                // the source settles it: `charge > ceiling` is a line about the charge.
                return new ComparedTerms(on.term(), against.term(), carriers,
                        holdsAtTheLine(comparison.op()),
                        holdsAtTheLine(comparison.op()) == !onIsAbove(comparison.op()), Count.ZERO);
            }
        }
        return fromTheForm(read, reads, symbols);
    }

    /**
     * The two positions on the orders they are read and written on, or null where they are not two
     * positions a distance runs between.
     *
     * <p>Three things make them one, and each of them is refused here rather than further down. One
     * position is not two, and {@code a > a} names one twice — read as a distance it would be a line
     * at nowhere between a position and itself. A position this reading has no order for is one
     * nothing can be written at. And two orders that share no counts have no difference: a whole
     * number of days and a whole number is not a number of anything, so such a pair is left to be
     * read as the form it is, which carries the conversion in its coefficients.
     *
     * <p>Which is why the answer is a carrier apiece and not one for the pair. A distance between
     * two positions written back differently — a decimal against a whole number is the pair that
     * exists — is still one distance, and it is only the writing that differs.
     */
    private static Map<NumericTerm, Carrier> aDistanceBetween(NumericTerm on, Carrier here,
                                                              NumericTerm against, Carrier there) {
        if (on == null || against == null || here == null || there == null || on.equals(against)) {
            return null;
        }
        // One order, or two whose counts are the same numbers. The first admits the pair that has no
        // counts at all: two strings stand no measurable distance apart and still stand one above
        // the other, which is a line this reading keeps.
        if (!here.equals(there) && !here.sharesCountSpaceWith(there)) {
            return null;
        }
        Map<NumericTerm, Carrier> both = new LinkedHashMap<>();
        both.put(on, here);
        both.put(against, there);
        return both;
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
    private static ComparedTerms fromTheForm(AffineReading read, InputReads reads,
                                             Symbols symbols) {
        if (read == null || !read.orders()) {
            return null;
        }
        NumericTerm[] two = read.twoCoordinates();
        if (two == null) {
            return null;
        }
        // Here the orders come from the reading of the declarations and from nowhere else. A term
        // the arithmetic produced has no expression that names it, so there is nothing to take a
        // type off — which is the whole of what went wrong when one was taken off the comparison.
        Map<NumericTerm, Carrier> carriers = aDistanceBetween(
                two[0], reads.read().carrierOf(two[0], symbols),
                two[1], reads.read().carrierOf(two[1], symbols));
        // And here the counts are asked for, which the reading above does not ask. A form holds the
        // two apart by a number it read off the rule, and a number of nothing is not a distance —
        // where the pair meets is the only place such a rule could cut, and that is the line the
        // reading above draws.
        if (carriers == null || !carriers.get(two[0]).counts()) {
            return null;
        }
        ComparisonClaim.Cut cut = (ComparisonClaim.Cut) read.claim();
        // The distance as the number it is. Held as a count of the carrier's steps, a threshold
        // that is not a whole number of them — which two decimals a rule holds half apart give —
        // was an exception thrown out of the measure.
        return new ComparedTerms(two[0], two[1], carriers, cut.holdsAtTheValue(),
                cut.valueBelongsBelow(), new Count(read.cut()));
    }

    /** Which side the left of the comparison is on where the comparison is satisfied. Read off the
     *  operator as written, since neither side is turned round here. */
    private static boolean onIsAbove(BinOp op) {
        return op == BinOp.GT || op == BinOp.GE;
    }

    /** Whether an operator orders its two sides, which {@code ==} and {@code /=} do not. */
    private static boolean ordersStrictly(BinOp op) {
        return switch (op) {
            case LT, LE, GT, GE -> true;
            case EQ, NE, AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
        };
    }

    private static boolean holdsAtTheLine(BinOp op) {
        return op == BinOp.LE || op == BinOp.GE;
    }
}
