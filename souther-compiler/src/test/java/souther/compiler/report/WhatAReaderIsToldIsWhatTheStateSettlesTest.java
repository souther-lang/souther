package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Demand;
import souther.compiler.partition.Generator;
import souther.compiler.partition.NotOwedReason;
import souther.compiler.partition.RepairShortfall;

import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The sentence for a state claims what the state settles, and nothing about what proved it.
 *
 * <p>Over every word of each closed vocabulary that says no row is owed or none was found, because a
 * reader acts on the sentence and not on the word: a proof that no value stands somewhere is said as
 * that, a search that did not settle it is never said as though it had, and a point the carrier
 * cannot name is said as one that cannot be written. Which of these a word is comes from the code
 * that acts on it — {@link Demand#excluded} and
 * {@link Generator.UnresolvedCombination.Reason#provesInfeasible} — so a word moved from one to the
 * other is a sentence that has to move with it.
 *
 * <p>And no sentence a model settles says the rules did it. A type with few values settles as much
 * as a rule does, with nothing written, and an author told the rules refused a point goes looking
 * for a rule that is not there.
 */
class WhatAReaderIsToldIsWhatTheStateSettlesTest {

    /** What a sentence may claim. */
    private enum Claim { NO_VALUE_STANDS, NOT_SETTLED, CANNOT_BE_WRITTEN }

    /** The forms a sentence takes to say that no value stands somewhere, and only those. */
    private static final List<String> NO_VALUE = List.of(
            "no value can", "which no value is", "for every row");

    @Test
    void aPointNotOwedIsSaidAsWhatSettledIt() {
        for (NotOwedReason each : NotOwedReason.values()) {
            Claim claim = new Demand.NotOwed(each).excluded()
                    ? Claim.NO_VALUE_STANDS : Claim.CANNOT_BE_WRITTEN;

            assertSays(claim, AdequacyReport.whyNotOwed(each), each);
            assertNamesNoRule(each.name(), each);
        }
    }

    @Test
    void aWordAComposingCameBackWithIsSaidAsAProofOnlyWhereItIsOne() {
        for (Generator.UnresolvedCombination.Reason each
                : Generator.UnresolvedCombination.Reason.values()) {
            Claim claim = each.provesInfeasible() ? Claim.NO_VALUE_STANDS : Claim.NOT_SETTLED;

            assertSays(claim, AdequacyReport.whyUnresolved(
                    new Generator.UnresolvedCombination(List.of("x"), each)), each);
            assertSays(claim, GeneratedRows.why(each), each);
            if (claim == Claim.NO_VALUE_STANDS) {
                assertNamesNoRule(each.name(), each);
            }
        }
    }

    @Test
    void aWayPastAGuardIsSaidAsOneNoRowGoesOnlyWhereNoValueCan() {
        for (RepairShortfall.Barrier each : RepairShortfall.Barrier.values()) {
            // Exhaustive, so a barrier added is one somebody says which of the two it is.
            Claim claim = switch (each) {
                case NO_VALUE_CAN_GO_THAT_WAY -> Claim.NO_VALUE_STANDS;
                case NOTHING_HOLDS_A_ROW_TO_IT, IT_WOULD_REWRITE_A_STATED_VALUE,
                     THE_ROW_ALREADY_DOES_ALL_OF_IT -> Claim.NOT_SETTLED;
            };

            assertSays(claim, GeneratedRows.why(each), each);
        }
    }

    private static void assertSays(Claim claim, String said, Object of) {
        boolean noValue = NO_VALUE.stream().anyMatch(said::contains);
        assertEquals(claim == Claim.NO_VALUE_STANDS, noValue,
                () -> of + " is " + claim + " and says: " + said);
        if (claim == Claim.CANNOT_BE_WRITTEN) {
            assertTrue(said.contains("cannot be written"), () -> of + " says: " + said);
        }
        if (claim == Claim.NO_VALUE_STANDS) {
            assertNamesNoRule(said, of);
        }
    }

    private static void assertNamesNoRule(String said, Object of) {
        assertFalse(said.toLowerCase(Locale.ROOT).replace('_', ' ').contains("rules"),
                () -> of + " says what proved it: " + said);
    }
}
