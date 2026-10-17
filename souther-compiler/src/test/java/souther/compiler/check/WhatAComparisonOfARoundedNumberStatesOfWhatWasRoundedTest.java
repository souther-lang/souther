package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;
import souther.runtime.CEILING;
import souther.runtime.DOWN;
import souther.runtime.FLOOR;
import souther.runtime.HALF_DOWN;
import souther.runtime.HALF_EVEN;
import souther.runtime.HALF_UP;
import souther.runtime.Rational;
import souther.runtime.RationalMath;
import souther.runtime.RoundingMode;
import souther.runtime.UP;

import java.math.BigInteger;
import java.util.EnumSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A comparison of a number rounded to a whole one states, of the number before rounding, exactly
 * what the rounding comes to.
 *
 * <p>Held against what the run time rounds, and not against the lines written down beside each way
 * of rounding: toward nought and away from it part at the sign of the threshold, and the half that
 * goes to the even number parts at its parity, so a line worked out as though every way were a
 * floor moved by a constant is right on one side of nought and wrong on the other.
 */
class WhatAComparisonOfARoundedNumberStatesOfWhatWasRoundedTest {

    /** Wider than every threshold this asks about, so nothing here is settled by the range. */
    private static final BigInteger WIDE = BigInteger.TEN.pow(12);

    /** Every number asked about is a whole number of these, so halves and between them are met. */
    private static final int QUARTERS = 4;

    @Test
    void theOperationsRoundingToAWholeNumberAreTheTwoNarrowings() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        for (String module : Set.of("Decimal", "Rational")) {
            BoundOperationFact.RoundsToAWholeNumber rounds = facts.roundsToAWholeNumber(
                    new ValueName.Stdlib.Operation(module, "toInt"));
            assertNotNull(rounds, module + ".toInt rounds to a whole number");
            assertEquals(EnumSet.allOf(WholeRounding.class), EnumSet.copyOf(rounds.ways().values()),
                    "every case of the policy is one way of rounding, and every way one case");
        }
    }

    /**
     * Every way of rounding, every relation, every threshold from below nought to above it, and
     * every quarter from well below to well above: what the statement says of the number before
     * rounding is whether the run time's rounding of it stands that way to the threshold.
     */
    @Test
    void theStatementHoldsOfTheNumberExactlyWhereItsRoundingStandsThatWayToTheThreshold() {
        for (WholeRounding way : WholeRounding.values()) {
            for (Rel rel : Rel.values()) {
                for (int k = -4; k <= 4; k++) {
                    ConstantComparison stated = RoundedToAWholeNumber.statementOf(way, rel,
                            BigInteger.valueOf(k), WIDE.negate(), WIDE);
                    for (int quarters = -24; quarters <= 24; quarters++) {
                        long rounded = RationalMath.toInt(runTimes(way),
                                Rational.of(BigInteger.valueOf(quarters),
                                        BigInteger.valueOf(QUARTERS)));
                        String asked = way + " " + rel + " " + k + " at " + quarters
                                + "/4: the run time rounds it to " + rounded;
                        assertEquals(rel.holds(Long.compare(rounded, k)),
                                holds(stated, way, quarters), asked);
                    }
                }
            }
        }
    }

    /**
     * A threshold past the ends of an Int is the same for every rounding a run reaches, since a
     * rounding past them aborts.
     */
    @Test
    void aThresholdPastTheEndsOfAnIntIsSettledByThem() {
        BigInteger least = BigInteger.valueOf(Long.MIN_VALUE);
        BigInteger most = BigInteger.valueOf(Long.MAX_VALUE);
        assertEquals(new ConstantComparison.Settled(false), RoundedToAWholeNumber.statementOf(
                WholeRounding.DOWN, Rel.GT, most, least, most));
        assertEquals(new ConstantComparison.Settled(true), RoundedToAWholeNumber.statementOf(
                WholeRounding.DOWN, Rel.GE, least, least, most));
        assertEquals(new ConstantComparison.Settled(true), RoundedToAWholeNumber.statementOf(
                WholeRounding.HALF_UP, Rel.LE, most, least, most));
    }

    /**
     * A line at a half of a threshold near the end of an Int is twice the threshold, which no
     * signed 64-bit number can say, and the comparison is not read rather than read as another.
     */
    @Test
    void aLineNoLongCanSayIsNotRead() {
        BigInteger least = BigInteger.valueOf(Long.MIN_VALUE);
        BigInteger most = BigInteger.valueOf(Long.MAX_VALUE);
        assertNull(RoundedToAWholeNumber.statementOf(WholeRounding.HALF_UP, Rel.GE,
                most.shiftRight(1).add(BigInteger.TEN), least, most));
        assertNotNull(RoundedToAWholeNumber.statementOf(WholeRounding.DOWN, Rel.GE,
                most.shiftRight(1).add(BigInteger.TEN), least, most));
    }

    private static RoundingMode runTimes(WholeRounding way) {
        return switch (way) {
            case HALF_UP -> HALF_UP.INSTANCE;
            case HALF_EVEN -> HALF_EVEN.INSTANCE;
            case HALF_DOWN -> HALF_DOWN.INSTANCE;
            case UP -> UP.INSTANCE;
            case DOWN -> DOWN.INSTANCE;
            case CEILING -> CEILING.INSTANCE;
            case FLOOR -> FLOOR.INSTANCE;
        };
    }

    /**
     * Whether {@code statement} holds of {@code quarters} quarters, taken twice where {@code way}'s
     * lines are at a half: a comparison of {@code q * times} with {@code b} is one of
     * {@code quarters * times} with {@code 4 * b}.
     */
    private static boolean holds(ConstantComparison statement, WholeRounding way, int quarters) {
        BigInteger taken = BigInteger.valueOf((long) quarters * (way.linesAtAHalf() ? 2 : 1));
        return switch (statement) {
            case ConstantComparison.Against(Rel rel, BigInteger against) ->
                    rel.holds(taken.compareTo(against.multiply(BigInteger.valueOf(QUARTERS))));
            case ConstantComparison.Settled(boolean holds) -> holds;
            case ConstantComparison.Both(var first, var second) ->
                    holds(first, way, quarters) && holds(second, way, quarters);
            case ConstantComparison.Either(var first, var second) ->
                    holds(first, way, quarters) || holds(second, way, quarters);
        };
    }
}
