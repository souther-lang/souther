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
 * The quantity a comparison over two positions cuts: how far the two stand apart.
 *
 * <p>{@link ComparedLine}'s sibling, and asked where that one came to nothing. A rule relating two
 * positions is not a partition of either (spec §what-a-position-admits), and that is an answer about
 * the classes rather than about the line.
 *
 * <p><b>The shape and not what the operator states about it.</b> Whether the rule orders the values
 * around the place the two meet or singles that place out is the claim's, and both are quantities
 * over the same pair. Told apart here, an equality over two positions had no realization at all
 * wherever the form's own reader wanted counting orders — so {@code s == t} over two strings, whose
 * meeting place is exactly what the pair's order has a number for, came back as a comparison this
 * compiler could not read.
 *
 * <p>Read the same way whoever wrote the comparison. A {@code guard} and a comparison in an
 * {@code ensures} draw the same line between the same two positions; what differs is what meeting it
 * takes, and that is the origin's to answer rather than this one's.
 *
 * <p>Asked of the orders and not of the types. A type is not what makes a line measurable: an
 * enumeration's case is comparable on its sum's order while carrying no places of its own, and two
 * newtypes of one base are two types whose values are ordered alike. What both positions can be read
 * as is the order, so that is what is asked about — and what is asked of the pair is that their
 * counts are one arithmetic, which is narrower than their being one order and wider than their being
 * one type.
 *
 * <p><b>The positions' orders, and never the operands'.</b> The two agree wherever a rule names its
 * positions itself, and part company the moment an operation stands between them: the operands of
 * {@code Date.daysBetween(a, b) > 10} are whole numbers and its positions hold dates. Read off the
 * comparison, both positions were written back and read off a row as whole numbers, and the border
 * could be met by no row and composed for by none (#1018). Nothing here reads an operand's type, and
 * the guard that used to — the two operands being of one order — was about neither position.
 *
 * @param stepsApart     how far apart the rule holds them, as a number on the carrier's counts.
 *                       Zero where the rule cuts where they meet, which is every comparison written
 *                       as one position against another. A number and not a count of steps: an order
 *                       with no smallest step still holds its values a distance apart
 */
record ComparedTerms(NumericTerm.FromOnePosition on, NumericTerm.FromOnePosition against,
                     Map<NumericTerm, souther.compiler.inputs.TermOrders> carriers,
                     Count stepsApart) {

    /**
     * The two positions {@code comparison} names, or null where it names no such pair.
     *
     * <p>Only where the comparison orders its two sides. This reading is reached where the
     * arithmetic stopped, and an equality between two things it could not read is a comparison
     * nothing here has taken apart at all — the canonical form is what says a pair is a pair, and
     * it had no answer.
     */
    static ComparedTerms asWritten(Core.Binary comparison,
                                   souther.compiler.inputs.InputDomain inputs,
                                   souther.compiler.inputs.Quantities quantities, InputReads reads,
                                   Symbols symbols) {
        if (ordersStrictly(comparison.op())) {
            GuardThresholds.Named on =
                    GuardThresholds.namedBy(comparison.left(), inputs, quantities, reads, symbols);
            GuardThresholds.Named against =
                    GuardThresholds.namedBy(comparison.right(), inputs, quantities, reads, symbols);
            // A distance runs between two positions, so each side has to be a number one answers.
            NumericTerm.FromOnePosition here = on == null ? null : on.term().atOnePosition();
            NumericTerm.FromOnePosition there =
                    against == null ? null : against.term().atOnePosition();
            Map<NumericTerm, souther.compiler.inputs.TermOrders> carriers =
                    here == null || there == null ? null
                            : aDistanceBetween(here, on.orders(), there, against.orders());
            if (carriers != null) {
                // The subject is the one the author wrote on the left, which the canonical form
                // keeps too. Which of the two a line is named by is not something to derive where
                // the source settles it: `charge > ceiling` is a line about the charge.
                return new ComparedTerms(here, there, carriers, Count.ZERO);
            }
        }
        return null;
    }

    /**
     * The two positions on the orders they are read and written on, or null where they are not two
     * positions a distance runs between.
     *
     * <p>Three things make them one, and each of them is a classification rather than a complaint:
     * a pair refused here is read as whatever it is instead, and an arithmetic form is what it is
     * instead. One position is not two, and {@code a > a} names one twice. A position this reading
     * has no order for is one nothing can be written at. And two orders that share no counts have no
     * difference — a whole number of days and a whole number is not a number of anything — so such a
     * pair is left to the form it is, which carries the conversion in its coefficients.
     *
     * <p>Whether two orders make such a pair is {@link Carrier#standsAgainst}'s to say, and it is
     * what refuses a distance built out of a pair that is not one. Classifying and refusing are two
     * jobs and one rule, so the rule is in one place and neither writes it out again.
     *
     * <p>Which is why the answer is a carrier apiece and not one for the pair. A distance between
     * two positions written back differently — a decimal against a whole number is the pair that
     * exists — is still one distance, and it is only the writing that differs.
     */
    private static Map<NumericTerm, souther.compiler.inputs.TermOrders> aDistanceBetween(
            NumericTerm on, souther.compiler.inputs.TermOrders here,
            NumericTerm against, souther.compiler.inputs.TermOrders there) {
        if (on == null || against == null || here == null || there == null
                || here.answered() == null || there.answered() == null
                || on.equals(against) || !here.answered().standsAgainst(there.answered())) {
            return null;
        }
        Map<NumericTerm, souther.compiler.inputs.TermOrders> both = new LinkedHashMap<>();
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
    static ComparedTerms fromTheForm(AffineReading read,
                                     souther.compiler.inputs.Quantities quantities) {
        if (read == null || read.claim() instanceof ComparisonClaim.Nothing) {
            return null;
        }
        NumericTerm[] pair = read.twoCoordinates();
        if (pair == null) {
            return null;
        }
        // Both of them numbers a position answers, since a distance is between two positions.
        NumericTerm.FromOnePosition[] two = {
            pair[0].atOnePosition(), pair[1].atOnePosition(),
        };
        if (two[0] == null || two[1] == null) {
            return null;
        }
        // The orders come from the reading of the declarations, the way they do above. A term the
        // arithmetic produced has no expression naming it, so there is not even a type here to take
        // one off — which is the whole of what went wrong when one was taken off the comparison.
        souther.compiler.inputs.TermOrders hereOn = quantities.ordersOf(two[0]);
        souther.compiler.inputs.TermOrders thereOn = quantities.ordersOf(two[1]);
        Carrier here = hereOn.answered();
        Carrier there = thereOn.answered();
        // Whether the order has a place at the number the rule wrote is the order's own answer and
        // is asked where the quantity is built ({@link LevelSpace#canCutAt}). Asked here as "do
        // these counts count", a property of the values stood in for a property of the places: two
        // strings stand no measurable distance apart and are still one above the other, so the
        // place they meet is a line — and this refused it, leaving the spelling to draw one.
        if (here == null) {
            return null;
        }
        Map<NumericTerm, souther.compiler.inputs.TermOrders> carriers =
                aDistanceBetween(two[0], hereOn, two[1], thereOn);
        if (carriers == null) {
            return null;
        }
        // The distance as the number it is. Held as a count of the carrier's steps, a threshold
        // that is not a whole number of them — which two decimals a rule holds half apart give —
        // was an exception thrown out of the measure.
        return new ComparedTerms(two[0], two[1], carriers, new Count(read.cut()));
    }

    /** Whether an operator orders its two sides, which {@code ==} and {@code /=} do not. */
    private static boolean ordersStrictly(BinOp op) {
        return switch (op) {
            case LT, LE, GT, GE -> true;
            case EQ, NE, AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
        };
    }
}
