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
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

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
        List<RuleRequirement.Excluded> readOff = excludedByReading();
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

    /**
     * Every sentence a proof is said in, whole and as a reader meets it.
     *
     * <p>The claim above is read from {@link NoValue}, which is where the sentences take it from,
     * so it says nothing of how the clause sits in the sentence around it. Written out here, apart
     * from the code that builds them, a clause put where a noun belongs is a sentence that reads
     * wrong in this file too. Exhaustive over each vocabulary, so a word added is one somebody writes
     * the sentence of — or says it is no proof.
     */
    @Test
    void everySentenceAProofIsSaidInReadsAsWritten() {
        for (Generator.UnresolvedCombination.Reason each
                : Generator.UnresolvedCombination.Reason.values()) {
            String[] said = switch (each) {
                case NO_VALUE_CAN_STAND_THERE -> new String[] {
                        "no value can stand at x",
                        "no value can stand here"};
                case ONE_POSITION_CANNOT_BE_BOTH -> new String[] {
                        "x would need one position to be two things at once, so no value can stand"
                                + " there",
                        "it would need one position to be two things at once, so no value can stand"
                                + " here and there is no row to write"};
                case A_CONDITION_NEVER_COMES_OUT_THAT_WAY -> new String[] {
                        "x is past a condition that comes out the other way for every row, so no"
                                + " value can go that way",
                        "it is past a condition that comes out the other way for every row, so no"
                                + " value can go that way and there is no row to write"};
                case NOTHING_COMPOSES_ONE, ALL_CANDIDATES_REJECTED,
                     NOTHING_STANDS_IN_FOR_A_DEPENDENCY, A_TABLE_IS_WHAT_THIS_NEEDS,
                     THE_SEARCH_LEFT_SOMETHING_UNTRIED, NOTHING_TO_BUILD_AGAINST,
                     THE_WAY_IN_PLACES_AT_NO_CLASS, NO_VALUES_WERE_ASKED_FOR,
                     THE_POSITION_WAS_WITHHELD, THE_GROUP_WAS_NOT_OFFERED,
                     THE_ROWS_WERE_NOT_READ, THE_BLOCK_IS_AS_LONG_AS_IT_MAY_BE, LINKAGE_FAILED,
                     NO_CERTIFIED_WITNESS, NO_CANDIDATE_WAS_OFFERED,
                     NOT_ALL_CANDIDATES_COULD_BE_OFFERED,
                     NO_READING_OF_THE_LINE_COULD_BE_SEARCHED,
                     EVERY_ROW_THERE_REACHES_AN_UNREACHABLE -> null;
            };
            assertEquals(each.provesInfeasible(), said != null, () -> each + " is a proof");
            if (said != null) {
                assertEquals(said[0], AdequacyReport.whyUnresolved(
                        new Generator.UnresolvedCombination(List.of("x"), each)), each.name());
                assertEquals(said[1], GeneratedRows.why(each), each.name());
            }
        }
        for (NotOwedReason each : NotOwedReason.values()) {
            assertEquals(switch (each) {
                case NO_VALUE_CAN_STAND_THERE -> "excluded — no value can stand there";
                case THE_CARRIER_NAMES_NO_NEIGHBOUR ->
                        "this order names no value there, so the point cannot be written";
            }, AdequacyReport.whyNotOwed(each), each.name());
        }
        for (RepairShortfall.Barrier each : RepairShortfall.Barrier.values()) {
            String said = switch (each) {
                case NO_VALUE_CAN_GO_THAT_WAY -> "no value can go that way, so no row goes this way";
                case NOTHING_HOLDS_A_ROW_TO_IT, IT_WOULD_REWRITE_A_STATED_VALUE,
                     THE_ROW_ALREADY_DOES_ALL_OF_IT -> null;
            };
            if (said != null) {
                assertEquals(said, GeneratedRows.why(each), each.name());
            }
        }
        for (RuleRequirement.Excluded each : excludedByReading()) {
            assertEquals(switch (each) {
                case RuleRequirement.Excluded.OnePositionCannotBeBoth _ ->
                        "its way would need one position to be two things at once, so no value can"
                                + " go that way";
                case RuleRequirement.Excluded.AnArmNothingReaches _ ->
                        "its way goes through an arm, but no value can reach that arm, so the branch"
                                + " count is made without it";
                case RuleRequirement.Excluded.AComparisonOutcomeNothingReaches _ ->
                        "its way needs a comparison to come out one way, but no value can reach it"
                                + " coming out so";
                case RuleRequirement.Excluded.AConditionNeverComesOutThatWay _ ->
                        "its way goes past a condition that comes out the other way for every row,"
                                + " so no value can go that way";
                case RuleRequirement.Excluded.NoValueCanTakeIt _ ->
                        throw new AssertionError("said in the words the composings came back with");
            }, AdequacyReport.readOff(each), each.getClass().getSimpleName());
        }
    }

    /** One of each kind of rule the readings exclude before anything is composed. */
    private static List<RuleRequirement.Excluded> excludedByReading() {
        return List.of(
                new RuleRequirement.Excluded.OnePositionCannotBeBoth(
                        new Reachability.TwoAtOnce.Truths(TermPath.of("x"))),
                new RuleRequirement.Excluded.AnArmNothingReaches(
                        new CoverageSites.AsWritten(null, 0)),
                new RuleRequirement.Excluded.AComparisonOutcomeNothingReaches(
                        new ModelOccurrence(new SourceConstructOrigin(
                                new WrittenOwner.Body("m", "b"), 0, 0, SourceConstruct.BINARY),
                                ExpansionLineage.ORIGINAL), true),
                new RuleRequirement.Excluded.AConditionNeverComesOutThatWay(new OnTheWay.Settled(
                        new ConditionOccurrence("b", ConditionOccurrence.Reading.DIVIDING, 0),
                        null, false)));
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
