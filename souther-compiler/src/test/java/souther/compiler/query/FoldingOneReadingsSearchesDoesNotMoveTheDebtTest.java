package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.ReadingGap;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
 */
class FoldingOneReadingsSearchesDoesNotMoveTheDebtTest {

    /** Every measurement a reading of a point can be in, one of each. */
    private static List<Measurement<ItemAssessment.Coverage>> everyShape() {
        return List.of(
                new Measurement.Complete<>(new ItemAssessment.Coverage.Hit()),
                new Measurement.Complete<>(new ItemAssessment.Coverage.NoHit()),
                new Measurement.Partial<>(new ItemAssessment.Coverage.Hit(), truncated()),
                new Measurement.Partial<>(new ItemAssessment.Coverage.NoHit(), truncated()),
                new Measurement.Partial<>(new ItemAssessment.Coverage.NoHit(), unreadable()),
                new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NO_ROWS),
                new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.NOT_ASKED),
                new Measurement.NotMeasured<>(ItemAssessment.Coverage.NotAsked.ARMS_NOT_ASKED),
                new Measurement.FailedToMeasure<>(ItemAssessment.Coverage.CouldNotAsk.ARMS_UNREADABLE,
                        unreadable()));
    }

    /**
     * The fold and the debt agree, at every pair there is.
     *
     * <p>Every pair and not a chosen few, because the shapes are few enough to walk. What this
     * refuses is the fold deciding anything: it may only say the debt's answer back.
     */
    @Test
    void whatTheDebtSaysIsTheSameWhicheverWayThePairReachesIt() {
        List<String> apart = new ArrayList<>();
        for (Measurement<ItemAssessment.Coverage> a : everyShape()) {
            for (Measurement<ItemAssessment.Coverage> b : everyShape()) {
                ObligationCoverage read = ObligationCoverage.acrossTheReadings(List.of(a, b));
                ObligationCoverage folded = ObligationCoverage.acrossTheReadings(
                        List.of(ObligationCoverage.acrossOneReadingsSearches(a, b)));
                if (!read.equals(folded)) {
                    apart.add(a + " with " + b + ": read " + read + ", folded " + folded);
                }
            }
        }

        assertEquals(List.of(), apart,
                "a fold of two searches of one reading says what the debt says of the two");
    }

    /**
     * And it is the same either way round, so nothing turns on which search was walked first.
     *
     * <p>Over the pairs a run can produce. Two readings saying the build asked for nothing and that
     * it asked for no arms is not one of them — the first is said by every line of a run that
     * measured nothing, so a reading beside it saying anything else is two runs — and the debt's own
     * fold keeps whichever of those it saw last. That the fold here says the same is this test's
     * subject; that the debt does it at all is not, and it is written down where it belongs.
     */
    @Test
    void thePairIsTheSameWhicheverOfThemCameFirst() {
        List<String> apart = new ArrayList<>();
        for (Measurement<ItemAssessment.Coverage> a : everyShape()) {
            for (Measurement<ItemAssessment.Coverage> b : everyShape()) {
                if (bothSayNobodyAsked(a, b)) {
                    continue;
                }
                ObligationCoverage one = ObligationCoverage.acrossTheReadings(
                        List.of(ObligationCoverage.acrossOneReadingsSearches(a, b)));
                ObligationCoverage other = ObligationCoverage.acrossTheReadings(
                        List.of(ObligationCoverage.acrossOneReadingsSearches(b, a)));
                if (!one.equals(other)) {
                    apart.add(a + " with " + b + ": " + one + " one way, " + other + " the other");
                }
            }
        }

        assertEquals(List.of(), apart, "the searches of one reading are a set of facts about it");
    }

    /**
     * A row one of them saw is still seen, and what that reading went without is still said.
     *
     * <p>The one case where the fold keeps a measurement rather than writing one: a row found by a
     * reading that could not read everything is found, and what it could not read is a fact of its
     * own that a canonical answer would drop.
     */
    @Test
    void aRowSeenByAReadingThatWentWithoutSomethingKeepsWhatItWentWithout() {
        Measurement<ItemAssessment.Coverage> seen =
                new Measurement.Partial<>(new ItemAssessment.Coverage.Hit(), truncated());
        Measurement<ItemAssessment.Coverage> missed =
                new Measurement.Complete<>(new ItemAssessment.Coverage.NoHit());

        Measurement<ItemAssessment.Coverage> folded =
                ObligationCoverage.acrossOneReadingsSearches(seen, missed);

        assertEquals(seen, folded, "the row stands, and so does what the reading that saw it"
                + " could not read");
        assertTrue(ObligationCoverage.acrossTheReadings(List.of(folded))
                        instanceof ObligationCoverage.Witnessed,
                "and the debt reads it as a row at the point, which is what it is");
    }

    /** Two readings each saying a question was not put, for two different reasons — which no run
     *  produces, and which the debt's own fold answers by the one it saw last. */
    private static boolean bothSayNobodyAsked(Measurement<ItemAssessment.Coverage> a,
                                              Measurement<ItemAssessment.Coverage> b) {
        return a instanceof Measurement.NotMeasured<ItemAssessment.Coverage> one
                && b instanceof Measurement.NotMeasured<ItemAssessment.Coverage> two
                && one.why() != two.why()
                && ((ItemAssessment.Coverage.NotAsked) one.why()).mayHideARow()
                && ((ItemAssessment.Coverage.NotAsked) two.why()).mayHideARow();
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
