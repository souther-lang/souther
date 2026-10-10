package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;
import souther.runtime.Temporals;

import java.math.BigInteger;
import java.time.LocalDateTime;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

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

    @Test
    void theOperationsCountingWholeUnitsAreTheOnesHeldHere() {
        assertEquals(Set.<ValueName>of(new ValueName.Stdlib.Operation("DateTime", "minutesBetween")),
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
        long perUnit = DefaultBoundOperationFacts.get().countsWholeUnitsBetween(
                new ValueName.Stdlib.Operation("DateTime", "minutesBetween")).perUnit();
        assertEquals(60, perUnit);
        for (Rel rel : Rel.values()) {
            for (int n = -4; n <= 4; n++) {
                WholeUnitsBetween.Statement stated =
                        WholeUnitsBetween.statementOf(rel, BigInteger.valueOf(n), perUnit);
                for (int steps = -300; steps <= 300; steps++) {
                    long count = Temporals.minutesBetween(FROM, FROM.plusSeconds(steps));
                    String asked = "minutesBetween " + rel + " " + n + " at " + steps
                            + " seconds: the count is " + count;
                    assertEquals(rel.holds(Long.compare(count, n)), holds(stated, steps), asked);
                }
            }
        }
    }

    /** A count asked about far past what a long holds is a statement about a number, not a wrap. */
    @Test
    void aCountPastTheEndOfALongStatesASecondsThresholdPastIt() {
        BigInteger past = BigInteger.valueOf(Long.MAX_VALUE).add(BigInteger.TEN);
        WholeUnitsBetween.Statement.Steps steps = (WholeUnitsBetween.Statement.Steps)
                WholeUnitsBetween.statementOf(Rel.GE, past, 60);
        assertEquals(past.multiply(BigInteger.valueOf(60)), steps.against());
        WholeUnitsBetween.Statement.Steps low = (WholeUnitsBetween.Statement.Steps)
                WholeUnitsBetween.statementOf(Rel.GE, BigInteger.valueOf(Long.MIN_VALUE), 60);
        assertEquals(BigInteger.valueOf(Long.MIN_VALUE).multiply(BigInteger.valueOf(60))
                .subtract(BigInteger.valueOf(59)), low.against());
    }

    private static boolean holds(WholeUnitsBetween.Statement statement, long steps) {
        return switch (statement) {
            case WholeUnitsBetween.Statement.Steps(Rel rel, BigInteger against) ->
                    rel.holds(BigInteger.valueOf(steps).compareTo(against));
            case WholeUnitsBetween.Statement.Both(var first, var second) ->
                    holds(first, steps) && holds(second, steps);
            case WholeUnitsBetween.Statement.Either(var first, var second) ->
                    holds(first, steps) || holds(second, steps);
        };
    }
}
