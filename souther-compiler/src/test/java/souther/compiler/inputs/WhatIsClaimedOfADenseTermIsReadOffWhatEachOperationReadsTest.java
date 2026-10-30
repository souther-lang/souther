package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.DecimalOperation.Formed;
import souther.compiler.inputs.DecimalOperation.Worked;
import souther.compiler.inputs.DecimalOperation.Written;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Term;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumberRegion;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What rows built at the ends of a run find of a decimal operation holds of every number between
 * only for what the operation reads.
 *
 * <p>Whether a decimal operation has room turns on the scale a number is written at and not on how
 * large it is: nought and 168 are worked out against a factor at the floor of the range and
 * {@code 0.5} between them is not. A row is a row where the program gets to the end of working it
 * out, so a number with no room is no row and no counterexample; what is claimed of the numbers
 * that have a row is read off the operations:
 *
 * <ul>
 * <li>an operation reading the term asked of and nothing else has room at a number or has none,
 * whichever other term is put where;
 * <li>an operation reading it with another term has room by what the other is put at, which is no
 * fact about the number, and nothing is claimed;
 * <li>an operation reading the term put beside it is worked out over numbers chosen at no more than
 * the places a row is built at, and has room for all of them or not.
 * </ul>
 */
class WhatIsClaimedOfADenseTermIsReadOffWhatEachOperationReadsTest {

    private static final NumericDomain.Bounds HOURS = new NumericDomain.Bounds(
            Endpoint.inclusive(Count.of(0)), Endpoint.inclusive(Count.of(168)));

    private static Term<String> hours(String place, long weight) {
        return new Term<>(List.of(place), ExactRatio.of(weight), HOURS, HOURS, null, true,
                Granularity.DENSE, NumericDomain.Bounds.OPEN, place);
    }

    /** {@code 4h - s >= 0}, the hours from nought to 168 on both sides. */
    private static final List<Term<String>> TERMS = List.of(hours("h", 4), hours("s", -1));

    private static final Formed H = new Formed(Map.of("h", ExactRatio.ONE), ExactRatio.ZERO);
    private static final Formed S = new Formed(Map.of("s", ExactRatio.ONE), ExactRatio.ZERO);
    private static final Formed A = new Formed(Map.of("a", ExactRatio.ONE), ExactRatio.ZERO);
    private static final BigDecimal AT_THE_FLOOR = new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE);

    private static DecimalOperation product(DecimalOperation.Operand one,
                                            DecimalOperation.Operand two) {
        return new DecimalOperation(BinOp.MUL, List.of(one, two), List.of());
    }

    private static DecimalOperation sum(DecimalOperation.Operand one,
                                        DecimalOperation.Operand two) {
        return new DecimalOperation(BinOp.ADD, List.of(one, two), List.of());
    }

    private static Leaves left(int asked, DecimalOperation... operations) {
        return WhatARelationLeavesUndivided.leavesOf(TERMS, asked, ExactRatio.ZERO, Rel.GE,
                String::equals, (one, other) -> true, Granularity.DENSE, null, List.of(),
                new Operations(List.of(), List.of(operations), Told.EVERY));
    }

    /** {@code 4h - s >= 0} with {@code h} from {@code lowest} to nought and {@code s} nought. */
    private static Leaves leftOfNoughtWithTheHoursFrom(BigDecimal lowest) {
        return leftOfNought(lowest, BigDecimal.ZERO, Rel.GE);
    }

    /** {@code 4h - s} against nought as {@code relation}, with {@code h} from {@code lowest} to
     *  {@code highest} and {@code s} nought. */
    private static Leaves leftOfNought(BigDecimal lowest, BigDecimal highest, Rel relation) {
        return leftOfNought(lowest, highest, lowest, highest, relation);
    }

    /** The same, with {@code h} held to {@code lowest} to {@code highest} and shown to take
     *  {@code lowestTaken} to {@code highestTaken}. */
    private static Leaves leftOfNought(BigDecimal lowest, BigDecimal highest,
                                       BigDecimal lowestTaken, BigDecimal highestTaken,
                                       Rel relation) {
        return leftOfNought(1, lowest, highest, lowestTaken, highestTaken, relation);
    }

    /** The same, of the term at {@code asked}. */
    private static Leaves leftOfNought(int asked, BigDecimal lowest, BigDecimal highest,
                                       BigDecimal lowestTaken, BigDecimal highestTaken,
                                       Rel relation) {
        NumericDomain.Bounds held = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(lowest)), Endpoint.inclusive(Count.of(highest)));
        NumericDomain.Bounds taken = new NumericDomain.Bounds(Endpoint.inclusive(
                Count.of(lowestTaken)), Endpoint.inclusive(Count.of(highestTaken)));
        NumericDomain.Bounds nought = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(0)), Endpoint.inclusive(Count.of(0)));
        List<Term<String>> terms = List.of(
                new Term<>(List.of("h"), ExactRatio.of(4), held, taken, null, true,
                        Granularity.DENSE, NumericDomain.Bounds.OPEN, "h"),
                new Term<>(List.of("s"), ExactRatio.of(-1), nought, nought, null, true,
                        Granularity.DENSE, NumericDomain.Bounds.OPEN, "s"));
        DecimalOperation timesFour = product(H, new Written(new BigDecimal("4.0")));
        return WhatARelationLeavesUndivided.leavesOf(terms, asked, ExactRatio.ZERO, relation,
                String::equals, (one, other) -> true, Granularity.DENSE, null, List.of(),
                new Operations(List.of(), List.of(timesFour), Told.EVERY));
    }

    /**
     * A row stands a term at a value it is shown to take, and not at one it is only held to. Held
     * from minus one to one, {@code h} has rows either side of nought; shown to take only a number
     * at the floor of the range below nought, it has none there, and what it is held to says
     * nothing of that. Shown to take a tenth below nought, it has one.
     */
    @Test
    void aRowStandsATermWhereItIsShownToTakeAValueAndNotWhereItIsHeld() {
        BigDecimal minusOne = new BigDecimal("-1");
        BigDecimal atTheFloor = new BigDecimal(BigInteger.ONE.negate(), Integer.MAX_VALUE);
        assertInstanceOf(Leaves.Undivided.class,
                leftOfNought(minusOne, BigDecimal.ONE, minusOne, BigDecimal.ONE, Rel.GE));
        assertFalse(leftOfNought(minusOne, BigDecimal.ONE, atTheFloor, BigDecimal.ZERO, Rel.GE)
                instanceof Leaves.Undivided);
        assertInstanceOf(Leaves.Undivided.class, leftOfNought(minusOne, BigDecimal.ONE,
                new BigDecimal("-0.1"), BigDecimal.ZERO, Rel.GE));
    }

    /**
     * A strict relation fails at its line, so the row at nought shows only that side and the other
     * is a row past nought: {@code h} held to nought and below has none, and from below to above
     * has one.
     */
    @Test
    void aStrictRelationNeedsARowPastTheLineAsAnAllowingOneNeedsARowBeforeIt() {
        BigDecimal minusOne = new BigDecimal("-1");
        assertFalse(leftOfNought(minusOne, BigDecimal.ZERO, Rel.GT) instanceof Leaves.Undivided);
        assertInstanceOf(Leaves.Undivided.class,
                leftOfNought(minusOne, BigDecimal.ONE, Rel.GT));
        assertInstanceOf(Leaves.Undivided.class,
                leftOfNought(minusOne, BigDecimal.ONE, Rel.GE));
        assertFalse(leftOfNought(BigDecimal.ZERO, BigDecimal.ONE, Rel.GE)
                instanceof Leaves.Undivided);
    }

    /**
     * {@code 4h >= s} at {@code s} nought holds at nought and fails below it, so a value of
     * {@code s} is left either way only by a row of {@code h} on each side of nought. The row at
     * nought is a row of the line; the other is a row beside it.
     */
    @Test
    void aRowOnTheLineShowsOneSideOfItAndTheOtherSideNeedsARowOfItsOwn() {
        assertInstanceOf(Leaves.Undivided.class,
                leftOfNoughtWithTheHoursFrom(new BigDecimal("-1")));
    }

    /**
     * The only number {@code h} holds below nought is one at the floor of the range, at which the
     * product has no room. Nought is worked out and the side below it is not: no row is on it,
     * and {@code s} is not left either way.
     */
    @Test
    void aSideWithNoRowBuiltOnItIsNotShownThoughTheMathsReachesIt() {
        BigDecimal atTheFloor = new BigDecimal(BigInteger.ONE.negate(), Integer.MAX_VALUE);
        assertFalse(leftOfNoughtWithTheHoursFrom(atTheFloor) instanceof Leaves.Undivided);
    }

    /**
     * {@code 4h >= s} at {@code s} nought holds at nought and above and fails below it. Shown to
     * take, below nought, only a number at the floor of the range, {@code h} has no row there:
     * the run above nought is a class, and the run below it is a region no row is shown computed
     * in, which is neither a class nor a run the relation leaves either way.
     */
    @Test
    void aRunNoRowIsShownComputedInIsKeptApartFromTheRunsThatAre() {
        BigDecimal atTheFloor = new BigDecimal(BigInteger.ONE.negate(), Integer.MAX_VALUE);
        Leaves.Settled settled = assertInstanceOf(Leaves.Settled.class, leftOfNought(0,
                new BigDecimal("-1"), BigDecimal.ONE, atTheFloor, BigDecimal.ONE, Rel.GE));
        assertEquals(1, settled.runs().size());
        assertTrue(settled.runs().getFirst().holds());
        assertEquals(1, settled.noRowShownComputed().size());
        assertFalse(settled.noRowShownComputed().getFirst().holds());
        assertFalse(settled.leavesItsPlacesUndivided(null));
        // The numbers are the run itself, below nought and not at it, and nothing of the run
        // that is computed.
        assertEquals(Optional.of(NumberRegion.of(List.of(new NumberRegion.Run(
                        settled.noRowShownComputed().getFirst().from(),
                        ExactCut.exclusive(ExactRatio.ZERO))))),
                settled.numbersNotShownComputed());
    }

    @Test
    void everyRunBeingComputedLeavesNoRegionApart() {
        BigDecimal minusOne = new BigDecimal("-1");
        Leaves.Settled settled = assertInstanceOf(Leaves.Settled.class,
                leftOfNought(0, minusOne, BigDecimal.ONE, minusOne, BigDecimal.ONE, Rel.GE));
        assertEquals(List.of(), settled.noRowShownComputed());
        assertEquals(Optional.empty(), settled.numbersNotShownComputed());
    }

    @Test
    void anOperationReadingOnlyTheTermAskedOfLeavesTheNumbersWithARowToBeSaidOf() {
        DecimalOperation timesFour = product(H, new Written(new BigDecimal("4.0")));
        assertInstanceOf(Leaves.Settled.class, left(0, timesFour));
    }

    @Test
    void anOperationReadingTheTermPutBesideItIsWorkedOutOverNumbersChosenAtFewPlaces() {
        DecimalOperation timesFour = product(H, new Written(new BigDecimal("4.0")));
        assertInstanceOf(Leaves.Settled.class, left(1, timesFour));
    }

    /** {@code a - s >= 5} over amounts from nought with no end, the sum {@code s + 5.0} told. */
    private static Leaves leftOfAmountsAgainstASumOfTheOther(int asked) {
        return leftOfAmounts(asked, S);
    }

    /** The same with the sum {@code operand + 5.0} told. */
    private static Leaves leftOfAmounts(int asked, Formed operand) {
        return leftOfAmounts(asked, operand, null);
    }

    /** The same, with {@code s} held to {@code mostOfS} at the most, or to no most where null. */
    private static Leaves leftOfAmounts(int asked, Formed operand, Long mostOfS) {
        return leftOfAmounts(asked, mostOfS, sum(operand, new Written(new BigDecimal("5.0"))));
    }

    /** The same, with {@code worked} the operation told. */
    private static Leaves leftOfAmounts(int asked, Long mostOfS, DecimalOperation worked) {
        return leftOfAmounts(asked, mostOfS, worked, NumericDomain.Bounds.OPEN);
    }

    /** The same, with the order {@code a} is counted on stopping at {@code aRunsTo}. */
    private static Leaves leftOfAmounts(int asked, Long mostOfS, DecimalOperation worked,
                                        NumericDomain.Bounds aRunsTo) {
        return leftOfAmounts(asked, mostOfS, List.of(worked), aRunsTo);
    }

    /** The same, with {@code worked} the operations told, none of them or more. */
    private static Leaves leftOfAmounts(int asked, Long mostOfS, List<DecimalOperation> worked,
                                        NumericDomain.Bounds aRunsTo) {
        NumericDomain.Bounds amounts = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(0)), null);
        NumericDomain.Bounds partners = mostOfS == null ? amounts : new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(0)), Endpoint.inclusive(Count.of(mostOfS)));
        List<Term<String>> terms = List.of(
                new Term<>(List.of("a"), ExactRatio.ONE, amounts, amounts, null, true,
                        Granularity.DENSE, aRunsTo, "a"),
                new Term<>(List.of("s"), ExactRatio.of(-1), partners, partners, null, true,
                        Granularity.DENSE, NumericDomain.Bounds.OPEN, "s"));
        return WhatARelationLeavesUndivided.leavesOf(terms, asked, ExactRatio.of(-5), Rel.GE,
                String::equals, (one, other) -> true, Granularity.DENSE, null, List.of(),
                new Operations(List.of(), worked, Told.EVERY));
    }

    /**
     * With no operation at all nothing can stop a row, and a run with no end is asked at the edge
     * of what is built all the same: the rows there are the claim of the numbers between, and a
     * term whose order stops short of the edge has none. Reached, the run is shown as it was.
     */
    @Test
    void aRunWithNoEndAndNoOperationIsAskedAtTheEdgeOfWhatIsBuilt() {
        NumericDomain.Bounds stopsShort = new NumericDomain.Bounds(null,
                Endpoint.inclusive(Count.of(BigDecimal.TEN.pow(100))));
        assertNull(leftOfAmounts(0, null, List.of(), stopsShort));
        Leaves.Settled open = assertInstanceOf(Leaves.Settled.class,
                leftOfAmounts(0, null, List.of(), NumericDomain.Bounds.OPEN));
        assertEquals(1, open.runs().size());
        assertFalse(open.runs().getFirst().holds());
    }

    /**
     * The sum reads {@code s} and nothing of {@code a}, so it has room at a number of {@code s}
     * chosen at few places whichever number of {@code a} that is chosen for. A run of {@code a}
     * with no end is asked at the edge of what is built.
     */
    @Test
    void aRunWithNoEndIsAskedAtTheEdgeOfWhatIsBuiltWhenNoOperationReadsTheTermAskedOf() {
        assertInstanceOf(Leaves.Settled.class, leftOfAmountsAgainstASumOfTheOther(0));
    }

    /**
     * That the sum has room is not what shows a row on each side of the line at an {@code a}: the
     * {@code s} to stand at is what {@code a} comes to. A partner held to at most a hundred has
     * none past a hundred and five, so the far end of the run is not left either way but settled
     * true, and the end the run has is asked of what is left, which is the numbers from five to a
     * hundred and five.
     */
    @Test
    void aRunWithNoEndHasRowsOnBothSidesOnlyWhereThePartnerReachesTheLine() {
        Leaves.Settled bounded = assertInstanceOf(Leaves.Settled.class,
                leftOfAmounts(0, S, 100L));
        assertEquals(2, bounded.runs().size());
        assertNull(bounded.runs().getLast().to());
        assertTrue(bounded.runs().getLast().holds());
        assertEquals(ExactRatio.of(105), bounded.runs().getLast().from().at());
        Leaves.Settled open = assertInstanceOf(Leaves.Settled.class, leftOfAmounts(0, S, null));
        assertEquals(1, open.runs().size());
        assertFalse(open.runs().getFirst().holds());
    }

    /**
     * The room the sum has turns on the scale of the {@code s} it is worked out over, and the
     * {@code s} a row stands at is what {@code a} comes to beside the line, written at few places
     * however large {@code a} is. So rows a long way out, where no row was built, are computed as
     * those at the end are: {@code a} a thousand, a power of ten past thirty digits and past a
     * hundred thousand, each with an {@code s} just below and just above {@code a - 5}.
     */
    @Test
    void theSumIsWorkedOutOnTheRowsBesideTheLineHoweverFarOutTheTermAskedOfStands() {
        List<DecimalOperation> plusFive = List.of(sum(S, new Written(new BigDecimal("5.0"))));
        for (int digits : new int[] {3, 30, DecimalOperation.PLACES_A_ROW_IS_BUILT_AT, 100_000}) {
            ExactRatio far = ExactRatio.of(BigInteger.TEN.pow(digits));
            for (String beside : new String[] {"-5.1", "-4.9", "-5.0"}) {
                ExactRatio at = far.plus(ExactRatio.of(new BigDecimal(beside))).orNull();
                assertTrue(DecimalOperation.allCompleteAt(plusFive, Map.of("s", at)),
                        digits + " digits, " + beside);
            }
        }
    }

    /**
     * The edge of what is built is asked as an end is: a term whose order stops short of it takes
     * no value there, so no row is built at the edge and nothing is shown of the run, though the
     * end it has is asked and computes. Past the edge nothing is claimed, and a term that stops
     * before it is claimed of no further.
     */
    @Test
    void aRunWithNoEndIsAskedAtTheEdgeOfWhatIsBuiltAndNotShownWhereTheTermStopsShortOfIt() {
        DecimalOperation plusFive = sum(S, new Written(new BigDecimal("5.0")));
        NumericDomain.Bounds stopsShort = new NumericDomain.Bounds(null,
                Endpoint.inclusive(Count.of(BigDecimal.TEN.pow(100))));
        assertNull(leftOfAmounts(0, null, plusFive, stopsShort));
        NumericDomain.Bounds reachesIt = new NumericDomain.Bounds(null, Endpoint.inclusive(
                Count.of(new BigDecimal(BigInteger.TEN.pow(
                        DecimalOperation.PLACES_A_ROW_IS_BUILT_AT + 1)))));
        assertInstanceOf(Leaves.Settled.class, leftOfAmounts(0, null, plusFive, reachesIt));
    }

    /**
     * What makes the room of a sum independent of how large its operands are: a row is built only
     * from numbers written at no more places than {@link DecimalOperation#PLACES_A_ROW_IS_BUILT_AT},
     * before or after the point, so the scales a sum lines up are at most twice that apart
     * whatever the digits are. Asked over the edge of what is built and over magnitudes from one
     * to past a hundred thousand digits, for a sum, a difference and a product by a number
     * written at a few places.
     */
    @Test
    void theRoomOfAnOperationOverARowDoesNotTurnOnHowLargeItsOperandsAre() {
        int places = DecimalOperation.PLACES_A_ROW_IS_BUILT_AT;
        BigInteger large = BigInteger.TEN.pow(100_000).subtract(BigInteger.valueOf(7));
        Written fiveTenths = new Written(new BigDecimal("5.0"));
        for (BigInteger digits : new BigInteger[] {BigInteger.valueOf(7), large}) {
            for (int scale : new int[] {-places, -1, 0, 1, places}) {
                ExactRatio at = ExactRatio.of(new BigDecimal(digits, scale));
                for (BinOp op : new BinOp[] {BinOp.ADD, BinOp.SUB, BinOp.MUL}) {
                    DecimalOperation operation = new DecimalOperation(op,
                            List.of(S, fiveTenths), List.of());
                    assertTrue(DecimalOperation.allCompleteAt(List.of(operation),
                                    Map.of("s", at)),
                            op + " over " + digits.bitLength() + " bits at scale " + scale);
                }
            }
        }
    }

    /**
     * What the numbers between and past the point far out stand on: the numbers the partner is
     * stood at beside a line are written at few places however far out the line is, whether it
     * lies at a number of a few digits or of a hundred thousand, at a whole number or at a third
     * of one. So the sum lines up the scales it lined up at the end of a run, and the room it has
     * there is the room it has anywhere.
     */
    @Test
    void theNumbersStoodBesideALineAreWrittenAtFewPlacesHoweverFarOutTheLineIs() {
        List<DecimalOperation> plusFive = List.of(sum(S, new Written(new BigDecimal("5.0"))));
        ExactRatio third = ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3));
        for (int digits : new int[] {3, 300, DecimalOperation.PLACES_A_ROW_IS_BUILT_AT, 100_000}) {
            ExactRatio far = ExactRatio.of(BigInteger.TEN.pow(digits));
            for (ExactRatio line : new ExactRatio[] {far, far.plus(third).orNull()}) {
                List<ExactRatio> beside = DecimalPoints.besideTheLine(line,
                        ExactCut.inclusive(ExactRatio.ZERO), null);
                assertEquals(2, beside.size(), digits + " digits");
                for (ExactRatio each : beside) {
                    assertTrue(DecimalPoints.isBuiltAt(each), digits + " digits");
                    assertTrue(DecimalOperation.allCompleteAt(plusFive, Map.of("s", each)),
                            digits + " digits");
                }
            }
        }
    }

    /**
     * A number that needs more places after the point than a row is built at is no row, so no
     * sum over it is said to be worked out, though adding five tenths to it has room. A number
     * of many digits before the point is written whole and is a row. A sum with a number written
     * at the far edge of the scale range is not claimed over, nor is one told of it.
     */
    @Test
    void aNumberPastTheEdgeOfWhatIsBuiltIsNoRowAndNoSumWithItIsClaimed() {
        List<DecimalOperation> plusFive = List.of(sum(S, new Written(new BigDecimal("5.0"))));
        ExactRatio past = ExactRatio.of(new BigDecimal(BigInteger.ONE,
                DecimalOperation.PLACES_A_ROW_IS_BUILT_AT + 1));
        assertFalse(DecimalOperation.allCompleteAt(plusFive, Map.of("s", past)));
        ExactRatio manyDigits = ExactRatio.of(BigInteger.TEN.pow(
                DecimalOperation.PLACES_A_ROW_IS_BUILT_AT + 1));
        assertTrue(DecimalOperation.allCompleteAt(plusFive, Map.of("s", manyDigits)));
        DecimalOperation plusTheFar = sum(S, new Written(new BigDecimal(BigInteger.ONE,
                -Integer.MAX_VALUE)));
        assertFalse(DecimalOperation.allowAClaimOver(List.of(plusTheFar), "a", "s"));
        assertNull(leftOfAmounts(0, null, plusTheFar));
    }

    /** An operation reading {@code a} has room by the scale {@code a} is written at, which a run
     *  with no end does not say at its far side. */
    @Test
    void aRunWithNoEndIsNotShownWhenAnOperationReadsTheTermAskedOf() {
        assertNull(leftOfAmounts(0, A));
    }

    @Test
    void anOperationReadingBothTermsLeavesNothingClaimed() {
        DecimalOperation together = sum(H, S);
        assertNull(left(0, together));
        assertNull(left(1, together));
    }

    @Test
    void anOperationReadingTheTermPutBesideItAtTheFloorOfTheRangeLeavesNothingClaimed() {
        DecimalOperation atTheFloor = product(S, new Written(AT_THE_FLOOR));
        assertNull(left(0, atTheFloor));
    }

    @Test
    void anOperationWorkedOutOfBothIsReadAsBothThoughNoOperandNamesThem() {
        List<DecimalOperation> operations = List.of(product(H, new Written(BigDecimal.ONE)),
                sum(new Worked(0), S));
        assertFalse(DecimalOperation.allowAClaimOver(operations, "h", "s"));
        assertFalse(DecimalOperation.allowAClaimOver(operations, "s", "h"));
    }

    @Test
    void readsOfAnOperationAreThePlacesOfTheInputItIsWorkedOutOf() {
        List<DecimalOperation> operations = List.of(product(H, new Written(BigDecimal.ONE)),
                sum(new Worked(0), new Written(BigDecimal.TEN)), product(S, S));
        assertEquals(List.of(Set.of("h"), Set.of("h"), Set.of("s")),
                DecimalOperation.readsOf(operations));
    }

    @Test
    void aClaimIsAllowedOverNoOperationsAndOverOnesReadingNeitherTerm() {
        assertTrue(DecimalOperation.allowAClaimOver(List.of(), "h", "s"));
        assertTrue(DecimalOperation.allowAClaimOver(List.of(
                product(new Formed(Map.of("c", ExactRatio.ONE), ExactRatio.ZERO),
                        new Written(AT_THE_FLOOR))), "h", "s"));
    }

    @Test
    void aChainOfOperationsOverTheTermPutBesideItGrowsPastWhatIsShownRoomFor() {
        List<DecimalOperation> chain = new ArrayList<>();
        chain.add(product(S, S));
        for (int i = 1; i < 40_000; i++) {
            chain.add(product(new Worked(i - 1), S));
        }
        assertFalse(DecimalOperation.allowAClaimOver(chain, "h", "s"));
        assertTrue(DecimalOperation.allowAClaimOver(chain, "s", "h"));
    }
}
