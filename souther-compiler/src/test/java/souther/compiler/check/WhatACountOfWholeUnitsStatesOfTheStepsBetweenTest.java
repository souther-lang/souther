package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;
import souther.runtime.Temporals;

import java.math.BigInteger;
import java.time.LocalDateTime;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A comparison of a count of whole units states, of the steps between the two values, exactly what
 * the count comes to.
 *
 * <p>Held against what the run time answers, and not against a rule written down here that the
 * reading was derived from: the count drops what is left of a unit toward zero, so a second before
 * is no minute before, and a threshold worked out as though it were a floor is right for every pair
 * where the second is later and wrong for the rest.
 */
class WhatACountOfWholeUnitsStatesOfTheStepsBetweenTest {

    private static final LocalDateTime FROM = LocalDateTime.of(2026, 3, 14, 12, 0, 0);

    /** Wider than every number of steps this asks about, so nothing here is settled by the range. */
    private static final BigInteger WIDE = BigInteger.TEN.pow(12);

    private static final ValueName MINUTES_BETWEEN =
            new ValueName.Stdlib.Operation("DateTime", "minutesBetween");

    @Test
    void theOperationsCountingWholeUnitsAreTheOnesHeldHere() {
        assertEquals(Set.<ValueName>of(MINUTES_BETWEEN),
                DefaultBoundOperationFacts.get().countsWholeUnitsBetween(),
                "an operation counting whole units that is not held here is not held to the run time");
    }

    /**
     * Every relation, every count from below nought to above it, and every number of seconds from
     * well before to well after: what the statement says of the steps is whether the run time's own
     * count stands that way to the number.
     */
    @Test
    void theStatementHoldsOfTheStepsExactlyWhereTheCountStandsThatWayToTheNumber() {
        long perUnit = DefaultBoundOperationFacts.get().countsWholeUnitsBetween(MINUTES_BETWEEN)
                .perUnit();
        assertEquals(60, perUnit);
        for (Rel rel : Rel.values()) {
            for (int n = -4; n <= 4; n++) {
                ConstantComparison stated =
                        WholeUnitsBetween.statementOf(rel, BigInteger.valueOf(n), perUnit, WIDE);
                for (int steps = -300; steps <= 300; steps++) {
                    long count = Temporals.minutesBetween(FROM, FROM.plusSeconds(steps));
                    String asked = "minutesBetween " + rel + " " + n + " at " + steps
                            + " seconds: the count is " + count;
                    assertEquals(rel.holds(Long.compare(count, n)), holds(stated, steps), asked);
                }
            }
        }
    }

    /**
     * A count no two values can be as far apart as is the same for every pair, whatever number
     * stands for it.
     *
     * <p>Where that is decided is the range the values are counted over, and not a figure of this
     * reading's: a threshold past the end of a signed 64-bit number is one more number past it.
     */
    @Test
    void aCountPastWhatTheValuesReachIsSettledByTheirRange() {
        BigInteger widest = BigInteger.valueOf(1_000_000);
        BigInteger past = BigInteger.valueOf(Long.MAX_VALUE).add(BigInteger.TEN);
        assertEquals(new ConstantComparison.Settled(false),
                WholeUnitsBetween.statementOf(Rel.GE, past, 60, widest));
        assertEquals(new ConstantComparison.Settled(true), WholeUnitsBetween.statementOf(Rel.GE,
                BigInteger.valueOf(Long.MIN_VALUE), 60, widest));
        assertEquals(new ConstantComparison.Settled(true),
                WholeUnitsBetween.statementOf(Rel.LT, past, 60, widest));
    }

    /**
     * A threshold the range reaches and no signed 64-bit number can say is a comparison this does not
     * read, and it is not read as another one.
     */
    @Test
    void aThresholdInsideTheRangeBeyondALongIsNotRead() {
        BigInteger widest = BigInteger.TWO.pow(70);
        assertNull(WholeUnitsBetween.statementOf(Rel.GE, BigInteger.TWO.pow(62), 60, widest));
        assertInstanceOf(ConstantComparison.Against.class,
                WholeUnitsBetween.statementOf(Rel.GE, BigInteger.TEN, 60, widest));
    }

    private static boolean holds(ConstantComparison statement, long steps) {
        return switch (statement) {
            case ConstantComparison.Against(Rel rel, BigInteger against) ->
                    rel.holds(BigInteger.valueOf(steps).compareTo(against));
            case ConstantComparison.Settled(boolean holds) -> holds;
            case ConstantComparison.Both(var first, var second) ->
                    holds(first, steps) && holds(second, steps);
            case ConstantComparison.Either(var first, var second) ->
                    holds(first, steps) || holds(second, steps);
        };
    }
}
