package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.ConditionOccurrence;
import souther.compiler.partition.Demand;
import souther.compiler.partition.Generator;
import souther.compiler.partition.NotOwedReason;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.Reachability;
import souther.compiler.partition.RepairShortfall;
import souther.compiler.query.ClaimAnnotations;
import souther.compiler.query.RuleRequirement;

import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.stream.Collectors;

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
            Claim claim = each.provesNoRowGoes() ? Claim.NO_VALUE_STANDS : Claim.NOT_SETTLED;

            assertSays(claim, GeneratedRows.why(each), each);
        }
    }

    /**
     * A rule the readings settled before anything was composed is said as no value taking its way,
     * whichever reading settled it. The one the composings proved is said in their words, which the
     * composing words above already hold to this.
     */
    @Test
    void aRuleNoValueTakesIsSaidAsThatAndNotAsWhatShowedIt() {
        List<RuleRequirement.Excluded> readOff = List.of(
                new RuleRequirement.Excluded.OnePositionCannotBeBoth(
                        new Reachability.TwoAtOnce.Truths(TermPath.of("x"))),
                new RuleRequirement.Excluded.AnArmNothingReaches(
                        new CoverageSites.AsWritten(null, 0)),
                new RuleRequirement.Excluded.AConditionNeverComesOutThatWay(new OnTheWay.Settled(
                        new ConditionOccurrence("b", ConditionOccurrence.Reading.DIVIDING, 0),
                        null, false)));
        // Every kind the readings settle, which is every kind but the one composings prove.
        assertEquals(Arrays.stream(RuleRequirement.Excluded.class.getPermittedSubclasses())
                        .filter(kind -> kind != RuleRequirement.Excluded.NoValueCanTakeIt.class)
                        .collect(Collectors.toSet()),
                readOff.stream().map(Object::getClass).collect(Collectors.toSet()));
        for (RuleRequirement.Excluded each : readOff) {
            assertSays(Claim.NO_VALUE_STANDS, AdequacyReport.readOff(each), each.getClass());
        }
    }

    /** What a claim nothing settled is told: never in the words a proof is said in. */
    @Test
    void aClaimNothingSettledIsNeverSaidAsAProof() {
        for (ClaimAnnotations.Why each : ClaimAnnotations.Why.values()) {
            assertSays(Claim.NOT_SETTLED, AdequacyReport.unproven(each), each);
        }
    }

    private static void assertSays(Claim claim, String said, Object of) {
        boolean noValue = said.contains(NoValue.CAN);
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
