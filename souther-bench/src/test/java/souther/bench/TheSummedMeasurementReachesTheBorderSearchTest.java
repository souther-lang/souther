package souther.bench;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That the time per point the summed measurement reports is the time of a search that composed rows.
 *
 * <p>The figure is divided by the points the report owed a row at, and both halves of that can go
 * quiet without the number saying so. A report that stopped asking for rows is fast, and its time
 * per point falls as though the search had got cheaper; a report that started owing fewer points
 * divides a smaller total by fewer of them. So the timed round is held to having composed rows, and
 * the points it owed to growing with the months the way the figure is read as.
 *
 * <p>Through {@link SummedChoices#time} and not a compile of this test's own, so that what is held
 * is the round the figure is the time of. One round, since what a round reaches does not turn on
 * how warm the JIT is, and at the smallest sizes: the claim is about the shape and holds at any
 * size of it, and the large ones are what the measurement is for.
 */
class TheSummedMeasurementReachesTheBorderSearchTest {

    @Test
    void everySizeComposesRowsAndOwesMoreThanTheOneBefore() {
        SummedChoices.Reached before = null;
        for (int months = 1; months <= 3; months++) {
            SummedChoices.Reached reached = SummedChoices.time(months, 0, 1).reached();
            String at = "months=" + months + ": " + reached;
            assertTrue(reached.composed() > 0,
                    at + " — the report composed no row, so its time is not a search's");
            assertTrue(reached.distinct() > 0 && reached.distinct() <= reached.composed(),
                    at + " — the rows are not the rows composed at the points");
            assertTrue(reached.searches() >= reached.composed(),
                    at + " — a point a row was composed at was not searched");
            if (before != null) {
                assertTrue(reached.points() > before.points(),
                        at + " owes no more points than " + before
                                + ", so a month more is not what the figure is read against");
            }
            before = reached;
        }
    }
}
