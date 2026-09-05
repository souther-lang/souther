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
     * What the readings of one behavior's rows can come back as.
     *
     * <p>The half of the input the gates read. Nothing here decides what a reading comes to — that
     * is asked of the gates below — and these are what a behavior hands them: rows nobody wrote,
     * rows nothing came back from, rows read without the instrumentation that records what they
     * went through, and rows this run read.
     */
    private static List<Adequacy.RowReading> everyReadingOfTheRows() {
        return List.of(
                Adequacy.RowReading.NONE,
                readingThatMet(Incompleteness.Code.OBSERVATION_ABSENT),
                readingThatMet(Incompleteness.Code.INSTRUMENTATION_ABSENT),
                readingThatMet(Incompleteness.Code.VALUE_UNREADABLE),
                Adequacy.RowReading.NOT_ASKED);
    }

    private static Adequacy.RowReading readingThatMet(Incompleteness.Code code) {
        return Adequacy.RowReading.of(List.of(),
                List.of(Incompleteness.of(code, Incompleteness.Scope.BEHAVIOR, "b")));
    }

    /**
     * What two searches of one reading can each come to.
     *
     * <p>One reading is one line of one behavior in one run, so the gates are asked once and both
     * searches get that answer. Where the gates leave the rows to answer, the two searches can
     * differ — they composed over different regions — and what they differ in is the value and what
     * each went without.
     *
     * <p><b>The reasons come from the gates and not from a table here.</b> Which reason a reading
     * gives is settled by {@link Coverages#whyNothingWasReadAgainstTheLine}, and a population that
     * wrote the gates out again would be a second statement of them — green over a producer that
     * had stopped agreeing with it, which is the shape this file's own subject is about one layer
     * down.
     */
    private static List<Measurement<ItemAssessment.Coverage>> everySearchOfOneReading(
            Reading of, Adequacy.RowReading rows) {
        Measurement<ItemAssessment.Coverage> nothingWasRead =
                Coverages.whyNothingWasReadAgainstTheLine(
                        of.kind() == LineKind.A_FORK, rows, of.level());
        if (nothingWasRead != null) {
            return List.of(nothingWasRead);
        }
        // Nothing back from the gates is them leaving the rows to answer, which is the gates' own
        // way of saying it and not something read off the level here. What a search then comes to
        // is a row at the point or none, read to the end or as far as it got.
        return List.of(
                new Measurement.Complete<>(new ItemAssessment.Coverage.Hit()),
                new Measurement.Complete<>(new ItemAssessment.Coverage.NoHit()),
                new Measurement.Partial<>(new ItemAssessment.Coverage.Hit(), truncated()),
                new Measurement.Partial<>(new ItemAssessment.Coverage.NoHit(), truncated()),
                new Measurement.Partial<>(new ItemAssessment.Coverage.NoHit(), unreadable()));
    }

    /**
     * What the readings of one line in one run can each come to.
     *
     * <p>Beside the one above and not the same set. A line is read once per behavior carrying the
     * type, and two behaviors of one run hand the gates different readings of their rows — so what
     * two readings of one line can be is wider than what two searches of one reading can be, and a
     * law about one of them run over the other asks its subject to answer for pairs it never sees.
     */
    private static List<Measurement<ItemAssessment.Coverage>> everyReadingOfOneLine(Reading of) {
        List<Measurement<ItemAssessment.Coverage>> out = new ArrayList<>();
        for (Adequacy.RowReading rows : everyReadingOfTheRows()) {
            for (Measurement<ItemAssessment.Coverage> each : everySearchOfOneReading(of, rows)) {
                if (!out.contains(each)) {
                    out.add(each);
                }
            }
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
            for (Measurement<ItemAssessment.Coverage> shape : everyReadingOfOneLine(reading)) {
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
            for (Measurement<ItemAssessment.Coverage> shape : everyReadingOfOneLine(reading)) {
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
            for (Adequacy.RowReading rows : everyReadingOfTheRows()) {
                for (Measurement<ItemAssessment.Coverage> a
                        : everySearchOfOneReading(reading, rows)) {
                    for (Measurement<ItemAssessment.Coverage> b
                            : everySearchOfOneReading(reading, rows)) {
                        ObligationCoverage read =
                                ObligationCoverage.acrossTheReadings(List.of(a, b));
                        ObligationCoverage folded = ObligationCoverage.acrossTheReadings(
                                List.of(ObligationCoverage.acrossOneReadingsSearches(a, b)));
                        if (!read.equals(folded)) {
                            apart.add(reading + ": " + a + " with " + b + ": read " + read
                                    + ", folded " + folded);
                        }
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
            for (Adequacy.RowReading rows : everyReadingOfTheRows()) {
                for (Measurement<ItemAssessment.Coverage> a
                        : everySearchOfOneReading(reading, rows)) {
                    for (Measurement<ItemAssessment.Coverage> b
                            : everySearchOfOneReading(reading, rows)) {
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
            for (Adequacy.RowReading rows : everyReadingOfTheRows()) {
                for (Measurement<ItemAssessment.Coverage> a
                        : everySearchOfOneReading(reading, rows)) {
                    for (Measurement<ItemAssessment.Coverage> b
                            : everySearchOfOneReading(reading, rows)) {
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
            for (Measurement<ItemAssessment.Coverage> a : everyReadingOfOneLine(reading)) {
                for (Measurement<ItemAssessment.Coverage> b : everyReadingOfOneLine(reading)) {
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
     * What a debt says is what put it in the state it is in, and a reading with nothing to look at
     * did not.
     *
     * <p>The fold ranks the states, and inside the one state a reason decides — nothing was read —
     * the reasons that outrank a miss are the ones that could be hiding a row. So those are what
     * the debt says, the way an undecided one says what left it undecided rather than everything
     * every reading went without. A reading with no rows hides nothing: it neither takes the state
     * back nor joins the reasons that reached it.
     */
    @Test
    void aReadingWithNoRowsIsNotOneOfTheReasonsThePointIsOpen() {
        ObligationCoverage debt = ObligationCoverage.acrossTheReadings(List.of(
                new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NOT_ASKED),
                new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NO_ROWS)));

        assertEquals(new ObligationCoverage.NotMeasured(
                        UnaskedReasons.of(ItemAssessment.Coverage.NotAsked.NOT_ASKED)),
                debt,
                "the rows nobody looked at are why the point is open, and the behavior with none"
                        + " is not");
        assertFalse(debt.settled(), "and the point is open, because those rows may be at it");
    }

    /**
     * A surface that says one reason refuses an account of two, and does not pick from it.
     *
     * <p>The negative control on the projection, and it is needed because nothing produces two
     * today: a law over what the producers make would pass just as well against a projection that
     * quietly took the first. What is refused is exactly the defect this issue is about, one layer
     * along — an answer chosen from a set by whatever order it happened to be in.
     *
     * <p>Built here rather than folded to, because the carrier admits the pair and the fold does
     * not make one. What the carrier admits is a question about the reasons; what the fold makes is
     * a question about the readings, and this is about neither.
     */
    @Test
    void aSurfaceThatSaysOneReasonRefusesTwoRatherThanChoosing() {
        UnaskedReasons two = UnaskedReasons.ofAll(List.of(
                ItemAssessment.Coverage.NotAsked.NOT_ASKED,
                ItemAssessment.Coverage.NotAsked.NO_ROWS));

        assertEquals(2, two.reasons().size(), "the carrier holds both, which is what it is for");
        assertThrows(IllegalStateException.class, two::asOne,
                "and a surface with room for one says so rather than taking whichever is first");
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
