package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;
import souther.runtime.CEILING;
import souther.runtime.DOWN;
import souther.runtime.DecimalMath;
import souther.runtime.FLOOR;
import souther.runtime.HALF_DOWN;
import souther.runtime.HALF_EVEN;
import souther.runtime.HALF_UP;
import souther.runtime.Rational;
import souther.runtime.RationalMath;
import souther.runtime.RoundingMode;
import souther.runtime.UP;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.EnumSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

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
            BoundOperationFact.RoundsToAStep rounds = facts.roundsToAWholeNumber(
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
                                holds(stated, ExactRatio.of(BigInteger.valueOf(quarters),
                                        BigInteger.valueOf(QUARTERS))), asked);
                    }
                }
            }
        }
    }

    /**
     * A rounding at a scale is the rounding of the number taken in steps: every way of rounding,
     * every relation, scales on both sides of nought, thresholds on the steps and between them,
     * and numbers on a grid finer than any step asked about — what the statement says of the
     * number is whether the run time's {@code Decimal.round} of it stands that way to the
     * threshold.
     */
    @Test
    void aRoundingAtAScaleStatesWhatTheRunTimesRoundingDoes() {
        for (WholeRounding way : WholeRounding.values()) {
            for (Rel rel : Rel.values()) {
                for (int scale = -1; scale <= 2; scale++) {
                    for (int thousandths = -1250; thousandths <= 1250; thousandths += 125) {
                        BigDecimal threshold = BigDecimal.valueOf(thousandths, 3)
                                .movePointRight(Math.max(0, -scale) * 2);
                        ConstantComparison stated = RoundedToAWholeNumber.statementAtAScale(way,
                                rel, ExactRatio.of(threshold), BigInteger.valueOf(scale));
                        for (int fine = -1600; fine <= 1600; fine += 5) {
                            BigDecimal number = BigDecimal.valueOf(fine, 3)
                                    .movePointRight(Math.max(0, -scale) * 2);
                            BigDecimal rounded = DecimalMath.round(scale, runTimes(way), number);
                            String asked = way + " " + rel + " " + threshold + " at scale "
                                    + scale + ", " + number + " rounds to " + rounded;
                            assertEquals(rel.holds(rounded.compareTo(threshold)),
                                    holds(stated, ExactRatio.of(number)), asked);
                        }
                    }
                }
            }
        }
    }

    /** And the rounding itself, which a number made of an element is evaluated with, is the run
     *  time's: every way, every quarter. */
    @Test
    void aWayOfRoundingRoundsAsTheRunTimeDoes() {
        for (WholeRounding way : WholeRounding.values()) {
            for (int quarters = -24; quarters <= 24; quarters++) {
                ExactRatio number = ExactRatio.of(BigInteger.valueOf(quarters),
                        BigInteger.valueOf(QUARTERS));
                long rounded = RationalMath.toInt(runTimes(way),
                        Rational.of(BigInteger.valueOf(quarters), BigInteger.valueOf(QUARTERS)));
                assertEquals(BigInteger.valueOf(rounded), way.of(number),
                        way + " of " + quarters + "/4");
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

    /** A line at a half below a threshold near the end of an Int is held as the half it is. */
    @Test
    void aLineAtAHalfNearTheEndOfAnIntIsTheHalfItIs() {
        BigInteger least = BigInteger.valueOf(Long.MIN_VALUE);
        BigInteger most = BigInteger.valueOf(Long.MAX_VALUE);
        assertEquals(new ConstantComparison.Against(Rel.GE,
                        ExactRatio.of(most.shiftLeft(1).subtract(BigInteger.ONE), BigInteger.TWO)),
                RoundedToAWholeNumber.statementOf(WholeRounding.HALF_UP, Rel.GE, most, least,
                        most));
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

    /** Whether {@code statement} holds of the number {@code q}. */
    private static boolean holds(ConstantComparison statement, ExactRatio q) {
        return switch (statement) {
            case ConstantComparison.Against(Rel rel, ExactRatio against) ->
                    rel.holds(q.compareTo(against));
            case ConstantComparison.Settled(boolean holds) -> holds;
            case ConstantComparison.Both(var first, var second) ->
                    holds(first, q) && holds(second, q);
            case ConstantComparison.Either(var first, var second) ->
                    holds(first, q) || holds(second, q);
        };
    }
}
