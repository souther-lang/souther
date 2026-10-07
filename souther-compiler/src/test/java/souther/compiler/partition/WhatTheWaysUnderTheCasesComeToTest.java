package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The ways a container and the values it is handed are written under the cases of a sum, how far
 * the walk over them went, and whether a case nobody read leaves any of them open.
 *
 * <p>Read off a reach built here rather than one a model was read into, because the case that
 * matters most — a case whose reading stopped — is one no model in this repository reads into
 * without also stopping everything around it. The two cases are an optional's two, which is a
 * narrowing like any other to the walk: what it asks of a case is that two of them at one position
 * do not hold together.
 */
class WhatTheWaysUnderTheCasesComeToTest {

    private static final TermPath LEAD = TermPath.of("lead");
    private static final Refinement ONE = Refinement.of(new Case.Presence(true));
    private static final Refinement OTHER = Refinement.of(new Case.Presence(false));

    private static NameReach.Crossing crossing(String field, Refinement branch) {
        return new NameReach.Crossing(LEAD, field, branch, LEAD.refine(branch).then(field));
    }

    /** {@code fields} spread under both cases of the lead, every one of them read. */
    private static NameReach spreadUnderBoth(String... fields) {
        List<NameReach.Crossing> crossings = new ArrayList<>();
        for (String field : fields) {
            crossings.add(crossing(field, ONE));
            crossings.add(crossing(field, OTHER));
        }
        return new NameReach(crossings, List.of(), List.of());
    }

    /** The name read under one case and stopped under the other. */
    private static NameReach stoppedUnderTheOther(String field) {
        return new NameReach(List.of(crossing(field, ONE)), List.of(),
                List.of(new NameReach.NotStanding(LEAD, field, OTHER,
                        new BlockReason.TypeUnresolved())));
    }

    private static ContentsAsked holding(String container, String value) {
        return new ContentsAsked(List.of(new ContentsAsked.Asked(
                LEAD.then(container), LEAD.then(value), true)));
    }

    @Test
    void aCaseWhoseReadingStoppedIsNoWayAndLeavesTheRestOpen() {
        WhereANameIsWritten written = WhereANameIsWritten.of(stoppedUnderTheOther("campaigns"),
                LEAD.then("campaigns"), Requirements.NONE, _ -> true);

        assertEquals(List.of(LEAD.refine(ONE).then("campaigns")),
                written.places().stream().map(WhereANameIsWritten.Place::position).toList());
        assertTrue(written.someNotWorkedOut());
    }

    /**
     * A row already the case that was read is no row of the case that was not: nothing it could be
     * is left open, so what its ways come to may be a proof.
     */
    @Test
    void aCaseWhoseReadingStoppedLeavesNothingOpenForARowThatIsAnotherCase() {
        Requirements alreadyOne = Requirements.NONE.and(LEAD, ONE);
        WhereANameIsWritten written = WhereANameIsWritten.of(stoppedUnderTheOther("campaigns"),
                LEAD.then("campaigns"), alreadyOne, _ -> true);

        assertEquals(List.of(LEAD.refine(ONE).then("campaigns")),
                written.places().stream().map(WhereANameIsWritten.Place::position).toList());
        assertFalse(written.someNotWorkedOut());
        assertFalse(holding("campaigns", "campaign")
                .underTheCases(stoppedUnderTheOther("campaigns"), alreadyOne).someNotWorkedOut());
    }

    @Test
    void aCaseWhoseReadingStoppedIsOpenForTheRowsTheWayGoesThrough() {
        assertTrue(holding("campaigns", "campaign")
                .underTheCases(stoppedUnderTheOther("campaigns"), Requirements.NONE)
                .someNotWorkedOut());
        assertFalse(holding("campaigns", "campaign")
                .underTheCases(spreadUnderBoth("campaigns"), Requirements.NONE)
                .someNotWorkedOut());
    }

    @Test
    void theFigureIsWhatKeptTheRestUntriedOnlyWhereTheWalkStoppedThere() {
        ContentsAsked.UnderTheCases under = holding("campaigns", "campaign")
                .underTheCases(spreadUnderBoth("campaigns"), Requirements.NONE);

        assertEquals(CompositionShortfall.of(Set.of(CompositionBudget.WAYS_UNDER_THE_CASES_TRIED)),
                under.untried(ContentsAsked.UnderTheCases.Walked.STOPPED_AT_THE_FIGURE));
        assertEquals(CompositionShortfall.NONE,
                under.untried(ContentsAsked.UnderTheCases.Walked.EVERY_WAY_TRIED));
    }

    @Test
    void twoNamesOfOneSumAreWrittenUnderOneCase() {
        ContentsAsked.UnderTheCases under = holding("campaigns", "campaign")
                .underTheCases(spreadUnderBoth("campaigns", "campaign"), Requirements.NONE);
        List<ContentsAsked> handed = new ArrayList<>();

        assertEquals(ContentsAsked.UnderTheCases.Walked.EVERY_WAY_TRIED,
                under.tryEach(each -> {
                    handed.add(each);
                    return false;
                }));
        assertEquals(List.of(holdingUnder(ONE), holdingUnder(OTHER)), handed);
    }

    private static ContentsAsked holdingUnder(Refinement branch) {
        return new ContentsAsked(List.of(new ContentsAsked.Asked(
                LEAD.refine(branch).then("campaigns"), LEAD.refine(branch).then("campaign"),
                true)));
    }

    @Test
    void theWaysStopWhereOneComposes() {
        ContentsAsked.UnderTheCases under = holding("campaigns", "campaign")
                .underTheCases(spreadUnderBoth("campaigns", "campaign"), Requirements.NONE);
        int[] handed = {0};

        assertEquals(ContentsAsked.UnderTheCases.Walked.COMPOSED,
                under.tryEach(_ -> ++handed[0] == 1));
        assertEquals(1, handed[0]);
    }

    /**
     * Names of four sums apart, each written under either of its two cases: more ways than the
     * figure, so the walk hands over as many as the figure and says it stopped there.
     */
    @Test
    void theWaysStopAtTheFigureAndSaySo() {
        int[] handed = {0};

        assertEquals(ContentsAsked.UnderTheCases.Walked.STOPPED_AT_THE_FIGURE,
                apart("first", "second", "third", "fourth").tryEach(_ -> {
                    handed[0]++;
                    return false;
                }));
        assertEquals(CompositionBudget.WAYS_UNDER_THE_CASES_TRIED.maximum(), handed[0]);
    }

    /** Three sums apart are as many ways as the figure, and every one of them is tried. */
    @Test
    void asManyWaysAsTheFigureAreEveryWay() {
        int[] handed = {0};

        assertEquals(ContentsAsked.UnderTheCases.Walked.EVERY_WAY_TRIED,
                apart("first", "second", "third").tryEach(_ -> {
                    handed[0]++;
                    return false;
                }));
        assertEquals(CompositionBudget.WAYS_UNDER_THE_CASES_TRIED.maximum(), handed[0]);
    }

    /** A container under each of {@code sums}, each spread under both cases of its own sum. */
    private static ContentsAsked.UnderTheCases apart(String... sums) {
        List<NameReach.Crossing> crossings = new ArrayList<>();
        List<ContentsAsked.Asked> asked = new ArrayList<>();
        for (String sum : sums) {
            TermPath at = TermPath.of(sum);
            crossings.add(new NameReach.Crossing(at, "held", ONE, at.refine(ONE).then("held")));
            crossings.add(new NameReach.Crossing(at, "held", OTHER,
                    at.refine(OTHER).then("held")));
            asked.add(new ContentsAsked.Asked(at.then("held"), TermPath.of("value"), true));
        }
        return new ContentsAsked(asked).underTheCases(
                new NameReach(crossings, List.of(), List.of()), Requirements.NONE);
    }
}
