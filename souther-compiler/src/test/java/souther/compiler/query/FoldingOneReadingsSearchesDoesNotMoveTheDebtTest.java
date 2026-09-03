package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasureReason;
import souther.compiler.partition.ReadingGap;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Putting two searches of one reading together does not change what the debt above them says.
 *
 * <p>A line read once and searched twice has to arrive at the gathering as one reading, so the two
 * measurements are made one. That is a second place where what the rows came to is decided, and the
 * thing to be afraid of is its parting from the first — a coverage semantics written twice is two
 * answers about one question, and which of them a reader gets would depend on how many times a
 * helper happened to be called.
 *
 * <p>So what is checked is not a table of cases but the relation between the two: whatever the pair
 * comes to when the debt reads them apart is what it comes to when the debt reads them folded. Held
 * as a table, every case anybody thought of would pass and the one nobody thought of is the one the
 * fold gets wrong.
 *
 * <p><b>Over the measurements a reading can be in, which is not every measurement that can be
 * written.</b> Which reason a reading gives for asking nothing is settled by the level the build
 * asked for and by whether a fork or an invariant drew the line, and a run has one level and a line
 * is of one kind. So the pairs are taken inside one of those and not across them: a pair drawn from
 * the whole product is a pair of readings from two runs, and a law over it asks the fold to answer
 * for a state nothing produces.
 */
class FoldingOneReadingsSearchesDoesNotMoveTheDebtTest {

    /** What drew the line, which decides which reasons a reading of it can give. */
    private enum LineKind { A_FORK, AN_INVARIANT }

    /** One run's level and one line's kind, which is what fixes the reasons below. */
    private record Reading(Adequacy.Level level, LineKind kind) {}

    private static List<Reading> everyReading() {
        List<Reading> out = new ArrayList<>();
        for (Adequacy.Level level : Adequacy.Level.values()) {
            for (LineKind kind : LineKind.values()) {
                out.add(new Reading(level, kind));
            }
        }
        return out;
    }

    /**
     * Every measurement a reading of one line can be in, under one level.
     *
     * <p>Written from the gates the reading goes through: a build that reads no rows says so before
     * anything is looked at, a build that runs no instrumented rows says it of a line a fork drew,
     * and what is left is what the rows came to. An invariant's line is never waiting on the arms,
     * which is why the two kinds have different sets.
     */
    private static List<Measurement<ItemAssessment.Coverage>> everyShape(Reading of) {
        if (!of.level().readsRows()) {
            return List.of(new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NOT_ASKED));
        }
        if (of.kind() == LineKind.A_FORK && !of.level().runsInstrumentedRows()) {
            return List.of(
                    new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.ARMS_NOT_ASKED));
        }
        List<Measurement<ItemAssessment.Coverage>> out = new ArrayList<>(List.of(
                new Measurement.Complete<>(new ItemAssessment.Coverage.Hit()),
                new Measurement.Complete<>(new ItemAssessment.Coverage.NoHit()),
                new Measurement.Partial<>(new ItemAssessment.Coverage.Hit(), truncated()),
                new Measurement.Partial<>(new ItemAssessment.Coverage.NoHit(), truncated()),
                new Measurement.Partial<>(new ItemAssessment.Coverage.NoHit(), unreadable()),
                new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NO_ROWS)));
        if (of.kind() == LineKind.A_FORK) {
            // The rows ran and what they went through was not recorded, which takes a run that
            // instruments them. An invariant's line has no arms to be waiting on.
            out.add(new Measurement.FailedToMeasure<>(
                    ItemAssessment.Coverage.CouldNotAsk.ARMS_UNREADABLE, unreadable()));
        }
        return List.copyOf(out);
    }

    /**
     * The population holds the states the laws below are about.
     *
     * <p>A negative control on the two of them. Every law here is over a set this file builds, and
     * a set that had lost the reasons a question was not put would pass all of them while saying
     * nothing — which is the shape the population had when it was one hand-written list.
     */
    @Test
    void everyReasonAQuestionIsNotPutForIsSomewhereInThePopulation() {
        List<ItemAssessment.Coverage.NotAsked> found = new ArrayList<>();
        for (Reading reading : everyReading()) {
            for (Measurement<ItemAssessment.Coverage> shape : everyShape(reading)) {
                if (shape instanceof Measurement.NotMeasured<ItemAssessment.Coverage> none) {
                    ItemAssessment.Coverage.NotAsked why =
                            (ItemAssessment.Coverage.NotAsked) none.why();
                    if (!found.contains(why)) {
                        found.add(why);
                    }
                }
            }
        }

        assertEquals(List.of(ItemAssessment.Coverage.NotAsked.values()).size(), found.size(),
                "every reason a reading gives for asking nothing is given by some reading: "
                        + found);
    }

    /** And no reading gives two of the reasons that are the run's, which is what lets the pairs
     *  below be taken inside one reading rather than across two runs. */
    @Test
    void noOneReadingCanGiveTwoOfTheRunsReasons() {
        for (Reading reading : everyReading()) {
            List<ItemAssessment.Coverage.NotAsked> ofTheRun = new ArrayList<>();
            for (Measurement<ItemAssessment.Coverage> shape : everyShape(reading)) {
                if (shape instanceof Measurement.NotMeasured<ItemAssessment.Coverage> none
                        && ((ItemAssessment.Coverage.NotAsked) none.why()).about()
                                == MeasureReason.About.THE_RUN) {
                    ofTheRun.add((ItemAssessment.Coverage.NotAsked) none.why());
                }
            }
            assertTrue(ofTheRun.size() <= 1,
                    reading + " gives more than one of the run's reasons: " + ofTheRun);
        }
    }

    /**
     * The fold and the debt agree, at every pair there is.
     *
     * <p>Every pair of one reading and not a chosen few. What this refuses is the fold deciding
     * anything: it may only say the debt's answer back.
     */
    @Test
    void whatTheDebtSaysIsTheSameWhicheverWayThePairReachesIt() {
        List<String> apart = new ArrayList<>();
        for (Reading reading : everyReading()) {
            for (Measurement<ItemAssessment.Coverage> a : everyShape(reading)) {
                for (Measurement<ItemAssessment.Coverage> b : everyShape(reading)) {
                    ObligationCoverage read = ObligationCoverage.acrossTheReadings(List.of(a, b));
                    ObligationCoverage folded = ObligationCoverage.acrossTheReadings(
                            List.of(ObligationCoverage.acrossOneReadingsSearches(a, b)));
                    if (!read.equals(folded)) {
                        apart.add(reading + ": " + a + " with " + b + ": read " + read
                                + ", folded " + folded);
                    }
                }
            }
        }

        assertEquals(List.of(), apart,
                "a fold of two searches of one reading says what the debt says of the two");
    }

    /** And it is the same either way round, so nothing turns on which search was walked first. */
    @Test
    void thePairIsTheSameWhicheverOfThemCameFirst() {
        List<String> apart = new ArrayList<>();
        for (Reading reading : everyReading()) {
            for (Measurement<ItemAssessment.Coverage> a : everyShape(reading)) {
                for (Measurement<ItemAssessment.Coverage> b : everyShape(reading)) {
                    ObligationCoverage one = ObligationCoverage.acrossTheReadings(
                            List.of(ObligationCoverage.acrossOneReadingsSearches(a, b)));
                    ObligationCoverage other = ObligationCoverage.acrossTheReadings(
                            List.of(ObligationCoverage.acrossOneReadingsSearches(b, a)));
                    if (!one.equals(other)) {
                        apart.add(reading + ": " + a + " with " + b + ": " + one + " one way, "
                                + other + " the other");
                    }
                }
            }
        }

        assertEquals(List.of(), apart, "the searches of one reading are a set of facts about it");
    }

    /**
     * The folded value is the same value either way round, and not only the same answer.
     *
     * <p>The law the projection above does not reach. What the debt says of the pair can be the
     * same while the measurement the fold writes differs, and the difference is read: a reading's
     * measurement says what the searches behind it went without, which a report prints. So a fold
     * that agreed with the debt and kept whichever it saw first would move that sentence with the
     * order the readings were walked in.
     */
    @Test
    void thePairIsTheSameValueWhicheverOfThemCameFirst() {
        List<String> apart = new ArrayList<>();
        for (Reading reading : everyReading()) {
            for (Measurement<ItemAssessment.Coverage> a : everyShape(reading)) {
                for (Measurement<ItemAssessment.Coverage> b : everyShape(reading)) {
                    Measurement<ItemAssessment.Coverage> one =
                            ObligationCoverage.acrossOneReadingsSearches(a, b);
                    Measurement<ItemAssessment.Coverage> other =
                            ObligationCoverage.acrossOneReadingsSearches(b, a);
                    if (!one.equals(other)) {
                        apart.add(reading + ": " + a + " with " + b + ": " + one + " one way, "
                                + other + " the other");
                    }
                }
            }
        }

        assertEquals(List.of(), apart, "the searches of one reading are a set of facts about it");
    }

    /**
     * What a debt comes to over the readings a run can give it fits the one reason a document says.
     *
     * <p>Beside the laws above rather than inside them. What a debt holds is every reason its
     * readings gave, which is what the fold is for; what a boundary item of the report has room for
     * is one. The two are separate contracts, and a producer that came to two reasons at one point
     * would leave the first green and this one red — which is where it is decided whether the
     * document gains room or the producer was wrong.
     *
     * <p>Over the readings of one line, which is what a debt is gathered from: a line is read once
     * per behavior carrying the type, every one of those readings is of the same run, and each is
     * whatever that behavior's rows came to.
     */
    @Test
    void whatTheReadingsOfOneRunComeToIsOneReasonADocumentCanSay() {
        for (Reading reading : everyReading()) {
            for (Measurement<ItemAssessment.Coverage> a : everyShape(reading)) {
                for (Measurement<ItemAssessment.Coverage> b : everyShape(reading)) {
                    ObligationCoverage debt = ObligationCoverage.acrossTheReadings(List.of(a, b));
                    if (debt instanceof ObligationCoverage.NotMeasured it) {
                        assertEquals(1, it.why().reasons().size(),
                                reading + ": " + a + " with " + b + " comes to " + it.why()
                                        + ", which a boundary item has no room for");
                    }
                }
            }
        }
    }

    /**
     * Two readings of one line saying two of the run's reasons is refused, and not answered.
     *
     * <p>The state the debt used to decide by walk order. It takes two runs to produce and no
     * reading here can be in it, so what closes it is the value refusing to be built rather than a
     * case in the fold — and a reader of a debt has no such state to consider.
     */
    @Test
    void aLineCannotHoldTwoOfWhatTheRunAsked() {
        assertThrows(IllegalArgumentException.class,
                () -> ObligationCoverage.acrossTheReadings(List.of(
                        new Measurement.NotMeasured<>(
                                ItemAssessment.Coverage.NotAsked.NOT_ASKED),
                        new Measurement.NotMeasured<>(
                                ItemAssessment.Coverage.NotAsked.ARMS_NOT_ASKED))),
                "a build is at one level and a line is of one kind");
    }

    /**
     * A row one of them saw is still seen, and what both of them went without is said.
     *
     * <p>Both, because the measurement is of the reading and the reading is both searches. Kept as
     * whichever saw the row, what the other could not read would be there or not depending on which
     * of them saw it — and a reader would be told a reading went without nothing on the strength of
     * the search that happened to come first.
     */
    @Test
    void aRowSeenByOneSearchKeepsWhatEitherOfThemWentWithout() {
        Measurement<ItemAssessment.Coverage> seen =
                new Measurement.Partial<>(new ItemAssessment.Coverage.Hit(), truncated());
        Measurement<ItemAssessment.Coverage> elsewhere =
                new Measurement.Partial<>(new ItemAssessment.Coverage.NoHit(), unreadable());

        Measurement<ItemAssessment.Coverage> folded =
                ObligationCoverage.acrossOneReadingsSearches(seen, elsewhere);

        assertEquals(new Measurement.Partial<>(new ItemAssessment.Coverage.Hit(),
                        truncated().union(unreadable())),
                folded,
                "the row stands, and what either search could not read is what the reading"
                        + " went without");
        assertTrue(ObligationCoverage.acrossTheReadings(List.of(folded))
                        instanceof ObligationCoverage.Witnessed,
                "and the debt reads it as a row at the point, which is what it is");
    }

    /**
     * A reading with nothing to look at is held beside one the run never asked, and does not take
     * it back.
     *
     * <p>The fold's own rule and not a claim about what a run reaches. The pair takes a build that
     * read no rows beside a behavior that has none, which the gates settle before the rows are
     * looked at — so what this pins is that the fold keeps both facts rather than that anything
     * hands it both.
     */
    @Test
    void aReadingWithNoRowsIsHeldBesideOneNobodyAsked() {
        ObligationCoverage debt = ObligationCoverage.acrossTheReadings(List.of(
                new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NOT_ASKED),
                new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NO_ROWS)));

        assertEquals(new ObligationCoverage.NotMeasured(UnaskedReasons.ofAll(List.of(
                        ItemAssessment.Coverage.NotAsked.NOT_ASKED,
                        ItemAssessment.Coverage.NotAsked.NO_ROWS))),
                debt,
                "both readings said why they read nothing, and the debt says both");
        assertFalse(debt.settled(), "and the point is still open, because one of them may hide a"
                + " row");
    }

    private static WeakeningSet truncated() {
        return WeakeningSet.of(new Weakening.BorderValueUnreadable(null,
                ReadingGap.of(Incompleteness.Code.VALUE_TRUNCATED)));
    }

    private static WeakeningSet unreadable() {
        return WeakeningSet.of(new Weakening.BorderValueUnreadable(null,
                ReadingGap.of(Incompleteness.Code.VALUE_UNREADABLE)));
    }
}
