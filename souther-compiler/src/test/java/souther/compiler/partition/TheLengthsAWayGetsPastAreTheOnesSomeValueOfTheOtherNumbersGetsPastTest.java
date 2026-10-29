package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.LengthsPastTheWay.Ends;
import souther.compiler.partition.LengthsPastTheWay.Lengths;
import souther.compiler.values.TextExtents;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The lengths a way gets past are those at which some value of every other number it names, held
 * between the ends the declarations leave it, meets every statement of the way.
 *
 * <p>Asked of an independent run: every assignment of a small range of lengths and of the other
 * numbers is tried, and the lengths some assignment meets all the statements at are the ones
 * the elimination is held to.
 */
class TheLengthsAWayGetsPastAreTheOnesSomeValueOfTheOtherNumbersGetsPastTest {

    private static final NumericTerm LENGTH = new NumericTerm.ValueOf(TermPath.of("length"));
    private static final NumericTerm N = new NumericTerm.ValueOf(TermPath.of("n"));
    private static final NumericTerm M = new NumericTerm.ValueOf(TermPath.of("m"));

    private static TakenConstraint statement(long constant, Rel rel, Map<NumericTerm, Long> weights) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        weights.forEach((term, weight) -> coefs.put(term, ExactRatio.of(weight)));
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant), coefs), rel);
    }

    private static Function<NumericTerm, Ends> between(long least, long greatest) {
        return _ -> new Ends(BigInteger.valueOf(least), BigInteger.valueOf(greatest));
    }

    /** The sum of a length and a number held to be above nought, with the number anywhere an
     *  {@code Int} is: every length has a number that gets past. */
    @Test
    void aSumAboveNoughtOfALengthAndANumberAnywhereInTheTypeIsGotPastAtEveryLength() {
        Lengths lengths = LengthsPastTheWay.of(LENGTH, List.of(
                statement(0, Rel.GT, Map.of(LENGTH, 1L, N, 1L)),
                statement(-Long.MAX_VALUE, Rel.LE, Map.of(LENGTH, 1L, N, 1L))),
                _ -> new Ends(BigInteger.valueOf(Long.MIN_VALUE), BigInteger.valueOf(Long.MAX_VALUE)));

        assertNotNull(lengths);
        assertTrue(lengths.holds(BigInteger.ZERO,
                BigInteger.valueOf(TextExtents.LONGEST_STRING)), lengths.toString());
    }

    /** The number held to the three greatest values of its type leaves only the lengths the
     *  sum can stay within the type at. */
    @Test
    void aNumberHeldNearTheGreatestLeavesOnlyTheShortLengths() {
        BigInteger greatest = BigInteger.valueOf(Long.MAX_VALUE);
        Lengths lengths = LengthsPastTheWay.of(LENGTH, List.of(
                statement(0, Rel.GT, Map.of(LENGTH, 1L, N, 1L)),
                statement(-Long.MAX_VALUE, Rel.LE, Map.of(LENGTH, 1L, N, 1L))),
                _ -> new Ends(greatest.subtract(BigInteger.TWO), greatest));

        assertEquals(BigInteger.TWO, lengths.most());
        assertTrue(lengths.holds(BigInteger.ZERO, BigInteger.TWO), lengths.toString());
        assertFalse(lengths.holds(BigInteger.ZERO, BigInteger.valueOf(3)), lengths.toString());
    }

    @Test
    void aStatementOfTheLengthAloneBoundsTheLengthsWithoutAnyOtherNumber() {
        assertEquals(new Lengths(BigInteger.valueOf(3), null), LengthsPastTheWay.of(LENGTH,
                List.of(statement(-3, Rel.GE, Map.of(LENGTH, 1L))), between(0, 0)));
    }

    @Test
    void aStatementNoNumberMeetsLeavesNoLength() {
        Lengths lengths = LengthsPastTheWay.of(LENGTH, List.of(
                statement(0, Rel.GT, Map.of(LENGTH, 1L, N, 1L)),
                statement(1, Rel.LE, Map.of(LENGTH, 1L, N, 1L))), between(-100, 100));

        assertNotNull(lengths);
        assertTrue(lengths.isEmpty(), lengths.toString());
    }

    /**
     * The lengths are those of strings: a sum the other number cannot bring below nought leaves
     * no length, and a length past the longest string is no length either.
     */
    @Test
    void aSumNoNumberCanBringBelowNoughtLeavesNoLengthAString() {
        Lengths lengths = LengthsPastTheWay.of(LENGTH, List.of(
                statement(1, Rel.LE, Map.of(LENGTH, 1L, N, 1L))),
                _ -> new Ends(BigInteger.ZERO, BigInteger.valueOf(Long.MAX_VALUE)));

        assertNotNull(lengths);
        assertTrue(lengths.isEmpty(), lengths.toString());
        assertNull(lengths.strings());
        assertFalse(lengths.holds(BigInteger.ZERO, BigInteger.ZERO), lengths.toString());
    }

    @Test
    void aLengthPastTheLongestStringIsNoLength() {
        Lengths lengths = LengthsPastTheWay.of(LENGTH, List.of(
                statement(-TextExtents.LONGEST_STRING - 1, Rel.GE, Map.of(LENGTH, 1L))),
                between(0, 0));

        assertNotNull(lengths);
        assertTrue(lengths.isEmpty(), lengths.toString());
    }

    @Test
    void theEndsGivenForALengthAreBroughtInToTheLengthsAStringHas() {
        assertEquals(new Lengths(BigInteger.ZERO, BigInteger.valueOf(TextExtents.LONGEST_STRING)),
                new Lengths(BigInteger.valueOf(-5), null));
        assertEquals(new Lengths(BigInteger.ONE, BigInteger.ZERO),
                new Lengths(null, BigInteger.valueOf(-1)));
        assertEquals(new Lengths(BigInteger.ONE, BigInteger.ZERO),
                new Lengths(BigInteger.valueOf(TextExtents.LONGEST_STRING + 1), null));
    }

    /** No length is left open by lengths that are none: every string is. */
    @Test
    void noLengthsLeaveEveryStringOpenAndShowNone() {
        Lengths none = new Lengths(null, BigInteger.valueOf(-1));

        assertEquals(1, none.outside().size());
        assertNull(none.strings());
        assertNull(none.stringsOutside());
    }

    @Test
    void aNumberWeighedMoreThanOnceIsNotTakenOut() {
        assertNull(LengthsPastTheWay.of(LENGTH, List.of(
                statement(0, Rel.GE, Map.of(LENGTH, 1L, N, 2L))), between(-10, 10)));
    }

    @Test
    void aNumberWithNoEndsGivenIsNotTakenOut() {
        assertNull(LengthsPastTheWay.of(LENGTH, List.of(
                statement(0, Rel.GE, Map.of(LENGTH, 1L, N, 1L))), _ -> null));
    }

    @Test
    void anInequalityBetweenNumbersIsNotAStatementOfAnInterval() {
        assertNull(LengthsPastTheWay.of(LENGTH, List.of(
                statement(0, Rel.NE, Map.of(LENGTH, 1L, N, 1L))), between(-10, 10)));
    }

    /**
     * Statements of a length and two other numbers, each weighed one or minus one, against every
     * assignment of a small range: the lengths the elimination gives are exactly the lengths some
     * assignment meets every statement at.
     */
    @Test
    void theLengthsAreExactlyThoseSomeAssignmentMeetsEveryStatementAt() {
        Random random = new Random(2810);
        Rel[] rels = {Rel.GE, Rel.GT, Rel.LE, Rel.LT, Rel.EQ};
        for (int round = 0; round < 400; round++) {
            List<TakenConstraint> system = new ArrayList<>();
            List<long[]> rows = new ArrayList<>();
            List<Rel> relations = new ArrayList<>();
            for (int each = 0, many = 1 + random.nextInt(4); each < many; each++) {
                long onLength = random.nextLong(7) - 3;
                long onN = random.nextLong(3) - 1;
                long onM = random.nextLong(3) - 1;
                long constant = random.nextLong(11) - 5;
                Rel rel = rels[random.nextInt(rels.length)];
                Map<NumericTerm, Long> weights = new LinkedHashMap<>();
                if (onLength != 0) {
                    weights.put(LENGTH, onLength);
                }
                if (onN != 0) {
                    weights.put(N, onN);
                }
                if (onM != 0) {
                    weights.put(M, onM);
                }
                system.add(statement(constant, rel, weights));
                rows.add(new long[] {constant, onLength, onN, onM});
                relations.add(rel);
            }
            long nLeast = -2 - random.nextLong(3);
            long nGreatest = 1 + random.nextLong(4);
            long mLeast = -2 - random.nextLong(3);
            long mGreatest = 1 + random.nextLong(4);
            Lengths lengths = LengthsPastTheWay.of(LENGTH, system,
                    term -> term.equals(N) ? new Ends(BigInteger.valueOf(nLeast),
                            BigInteger.valueOf(nGreatest))
                            : new Ends(BigInteger.valueOf(mLeast), BigInteger.valueOf(mGreatest)));
            if (lengths == null) {
                continue;
            }
            // Only lengths a string has: no string is shorter than nought.
            for (long length = 0; length <= 40; length++) {
                boolean some = false;
                for (long n = nLeast; n <= nGreatest && !some; n++) {
                    for (long m = mLeast; m <= mGreatest && !some; m++) {
                        some = meetsAll(rows, relations, length, n, m);
                    }
                }
                BigInteger at = BigInteger.valueOf(length);
                boolean given = !lengths.isEmpty() && lengths.least().compareTo(at) <= 0
                        && lengths.most().compareTo(at) >= 0;
                assertEquals(some, given, "round " + round + " length " + length + " "
                        + system + " gave " + lengths);
            }
        }
    }

    private static boolean meetsAll(List<long[]> rows, List<Rel> relations, long length, long n,
                                    long m) {
        for (int each = 0; each < rows.size(); each++) {
            long[] row = rows.get(each);
            long value = row[0] + row[1] * length + row[2] * n + row[3] * m;
            if (!relations.get(each).holds(Long.signum(value))) {
                return false;
            }
        }
        return true;
    }
}
