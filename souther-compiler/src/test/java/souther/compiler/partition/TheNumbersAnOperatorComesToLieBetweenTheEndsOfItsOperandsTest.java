package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The numbers a sum, a difference, a product or a negation comes to of numbers between two ends
 * each, and what a remainder by a written divisor comes to: the least and the greatest of every
 * pair of whole numbers between the ends, worked out one by one, and of every dividend.
 */
class TheNumbersAnOperatorComesToLieBetweenTheEndsOfItsOperandsTest {

    private static final int FROM = -4;
    private static final int TO = 4;

    /** The least and the greatest {@code op} comes to of every whole number of {@code left} and
     *  every one of {@code right}. */
    private static FormRange everyPair(BinOp op, FormRange left, FormRange right) {
        BigInteger least = null;
        BigInteger greatest = null;
        for (BigInteger a : wholeNumbersOf(left)) {
            for (BigInteger b : wholeNumbersOf(right)) {
                BigInteger c = switch (op) {
                    case ADD -> a.add(b);
                    case SUB -> a.subtract(b);
                    case MUL -> a.multiply(b);
                    default -> throw new IllegalArgumentException(op.toString());
                };
                least = least == null || c.compareTo(least) < 0 ? c : least;
                greatest = greatest == null || c.compareTo(greatest) > 0 ? c : greatest;
            }
        }
        return new FormRange(ExactRatio.of(least), ExactRatio.of(greatest));
    }

    private static List<BigInteger> wholeNumbersOf(FormRange range) {
        List<BigInteger> out = new ArrayList<>();
        for (BigInteger at = range.least().floor().orNull();
             at.compareTo(range.greatest().floor().orNull()) <= 0; at = at.add(BigInteger.ONE)) {
            out.add(at);
        }
        return out;
    }

    private static List<FormRange> everyRange() {
        List<FormRange> out = new ArrayList<>();
        for (int least = FROM; least <= TO; least++) {
            for (int greatest = least; greatest <= TO; greatest++) {
                out.add(new FormRange(ExactRatio.of(least), ExactRatio.of(greatest)));
            }
        }
        return out;
    }

    @Test
    void aSumADifferenceAndAProductLieBetweenTheLeastAndTheGreatestOfEveryPair() {
        Map<String, FormRange> expected = new LinkedHashMap<>();
        Map<String, FormRange> actual = new LinkedHashMap<>();
        for (BinOp op : List.of(BinOp.ADD, BinOp.SUB, BinOp.MUL)) {
            for (FormRange left : everyRange()) {
                for (FormRange right : everyRange()) {
                    String key = left + " " + op + " " + right;
                    expected.put(key, everyPair(op, left, right));
                    actual.put(key, FormRange.combined(op, left, right));
                }
            }
        }
        assertEquals(expected, actual);
    }

    @Test
    void aNegationLiesBetweenTheEndsNegated() {
        for (FormRange range : everyRange()) {
            assertEquals(everyPair(BinOp.SUB, new FormRange(ExactRatio.ZERO, ExactRatio.ZERO),
                    range), FormRange.negated(range), range::toString);
        }
    }

    @Test
    void whatIsNotKnownOfAnOperandIsNotKnownOfWhatItComesTo() {
        FormRange one = new FormRange(ExactRatio.ONE, ExactRatio.ONE);
        assertNull(FormRange.combined(BinOp.ADD, one, null));
        assertNull(FormRange.combined(BinOp.MUL, null, one));
        assertNull(FormRange.negated(null));
    }

    /** A remainder by each divisor lies from the least to the greatest remainder any dividend
     *  leaves, whatever the dividend's own numbers. */
    @Test
    void aRemainderLiesFromTheLeastToTheGreatestRemainderAnyDividendLeaves() {
        ValueName floorMod = ValueName.Stdlib.operation("Int", "floorMod");
        NumericTerm dividend = new NumericTerm.ValueOf(TermPath.of("x"));
        Map<Integer, FormRange> expected = new LinkedHashMap<>();
        Map<Integer, FormRange> actual = new LinkedHashMap<>();
        for (int divisor = 1; divisor <= 13; divisor++) {
            BigInteger least = null;
            BigInteger greatest = null;
            for (int x = -3 * divisor; x <= 3 * divisor; x++) {
                BigInteger r = BigInteger.valueOf(Math.floorMod(x, divisor));
                least = least == null || r.compareTo(least) < 0 ? r : least;
                greatest = greatest == null || r.compareTo(greatest) > 0 ? r : greatest;
            }
            expected.put(divisor, new FormRange(ExactRatio.of(least), ExactRatio.of(greatest)));
            actual.put(divisor, FormRange.ofARemainder(Quantity.RemainderOfADividend.ofTheInput(
                    floorMod, new LinearForm<>(ExactRatio.ZERO, Map.of(dividend, ExactRatio.ONE)),
                    BigInteger.valueOf(divisor))));
        }
        assertEquals(expected, actual);
    }
}
