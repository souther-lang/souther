package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.query.ItemAssessment.Coverage;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * One authored line is read at every position of every behavior carrying the type, and what the debt
 * came to is not any one of those readings.
 *
 * <p>Written against the fold rather than through a model, because what decides the answer is which
 * readings there are and a model reaches only the combinations it happens to produce. The case this
 * is for — a behavior nobody wrote a row for beside one whose rows were read to the end — is one no
 * model of a few lines puts together, and it is the one an implementation gets wrong.
 *
 * <p>The mistake it is against is reading the state and not the reason. Three of these readings are
 * one {@code NotMeasured} and they do not mean one thing: rows the build never looked at may be
 * standing at the point, and rows that do not exist cannot be.
 */
class WhatTheReadingsOfOneDebtComeToTogetherTest {

    /**
     * A row found anywhere settles the line, whatever the readings beside it went without.
     *
     * <p>First, and before anything is counted. A debt is discharged by evidence from any of its
     * readings — that is what makes the readings of one line one debt — so an accounting of what
     * went unread may not take back a row somebody wrote.
     */
    @Test
    void aRowFoundAtOneReadingSettlesTheDebt() {
        assertEquals(new ObligationCoverage.Witnessed(),
                ObligationCoverage.acrossTheReadings(List.of(
                        missed(), found(), unread())),
                "one reading is at the point, which is what the line asked for");
    }

    /**
     * A reading that may be hiding a row leaves the debt unsettled, however many read to the end.
     *
     * <p>The row could be at the position that went unread, so nothing here has shown there is none.
     * What the other readings established is kept beside it as the value — no row was seen — and the
     * measurement says the reading was not whole.
     */
    @Test
    void aReadingThatMayBeHidingARowLeavesTheDebtUnsettled() {
        ObligationCoverage across =
                ObligationCoverage.acrossTheReadings(List.of(missed(), unread()));

        assertInstanceOf(ObligationCoverage.Undecided.class, across,
                "the reading was not whole, so neither is the answer");
        assertEquals(new ObligationCoverage.Undecided(WEAKENED), across,
                "no row was seen at any of them, and this is what the reading went without");
    }

    /**
     * A reading with no rows to look at does not take back a miss another reading established.
     *
     * <p>The case the reasons are told apart for. A behavior nobody wrote a row for is not a place a
     * row could be hiding, so it says nothing about the line and the reading that read its rows to
     * the end still answers. Read as the state — nothing was measured, so nothing is known — a debt
     * carried by two behaviors went undecided as soon as one of them had no rows, and a build
     * stopped refusing a gap it had established.
     */
    @Test
    void aReadingWithNoRowsDoesNotUnsettleAMissBesideIt() {
        assertEquals(new ObligationCoverage.Missed(),
                ObligationCoverage.acrossTheReadings(List.of(noRows(), missed())),
                "the rows that exist were read and none is at the point");
    }

    /**
     * A build that asked for no measurement does take it back.
     *
     * <p>Beside the case above, which is the whole of what telling the reasons apart buys. Both are
     * a {@code NotMeasured} and only one of them could be holding the row: rows the build never
     * looked at exist and were not read, and rows nobody wrote do not exist.
     */
    @Test
    void aBuildThatLookedAtNothingDoesUnsettleAMissBesideIt() {
        assertEquals(new ObligationCoverage.NotMeasured(Coverage.NotAsked.NOT_ASKED),
                ObligationCoverage.acrossTheReadings(List.of(notAsked(), missed())),
                "the rows of the reading that was never made may be at the point");
    }

    /** Where every reading had nothing to look at, neither has the debt. */
    @Test
    void aDebtNoRowAnywhereCouldHaveAnsweredIsNotAMiss() {
        assertEquals(new ObligationCoverage.NotMeasured(Coverage.NotAsked.NO_ROWS),
                ObligationCoverage.acrossTheReadings(List.of(noRows(), noRows())));
    }

    /** A debt is what its readings came to, so there is no answer where there are none. */
    @Test
    void aDebtWithNoReadingsIsNotAnAnswer() {
        assertThrows(IllegalArgumentException.class,
                () -> ObligationCoverage.acrossTheReadings(List.of()));
    }

    /**
     * A reading made in part that found the row comes back as one a row is at, and not as one made
     * in part.
     *
     * <p>The state the fold's codomain does not have. A reading's coverage is a measurement of that
     * reading and may be both — what it could not read and what it did find are separate facts about
     * it — and a debt's cannot: a row found settles the line, so what the readings went without has
     * nothing left to weaken.
     */
    @Test
    void aReadingMadeInPartThatFoundTheRowIsWitnessedAndNotUndecided() {
        assertEquals(new ObligationCoverage.Witnessed(),
                ObligationCoverage.acrossTheReadings(List.of(
                        new Measurement.Partial<>(new Coverage.Hit(), WEAKENED))),
                "found is found, whatever the reading beside it went without");
    }

    /** A reading that found the row. */
    private static Measurement<Coverage> found() {
        return new Measurement.Complete<>(new Coverage.Hit());
    }

    /** A reading that read its rows to the end and found none at the point. */
    private static Measurement<Coverage> missed() {
        return new Measurement.Complete<>(new Coverage.NoHit());
    }

    /** A reading that did not run out, so the row may be behind what it could not read. */
    private static Measurement<Coverage> unread() {
        return new Measurement.Partial<>(new Coverage.NoHit(), WEAKENED);
    }

    /** A reading of a behavior nobody wrote a row for. */
    private static Measurement<Coverage> noRows() {
        return new Measurement.NotMeasured<>(Coverage.NotAsked.NO_ROWS);
    }

    /** A reading the build never asked for. */
    private static Measurement<Coverage> notAsked() {
        return new Measurement.NotMeasured<>(Coverage.NotAsked.NOT_ASKED);
    }

    private static final WeakeningSet WEAKENED =
            WeakeningSet.of(new Weakening.BodiesNotElaborated("example"));
}
