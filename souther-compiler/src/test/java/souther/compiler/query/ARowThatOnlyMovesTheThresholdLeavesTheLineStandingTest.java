package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.LinearQuantity;
import souther.compiler.partition.OrderedAffineBoundary;
import souther.compiler.partition.ReadingGap;
import souther.compiler.partition.StandingAtAPoint;
import souther.compiler.partition.WayToTheBorder;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What settles a line of the family is leaving no threshold on it standing, and a row that answers
 * the line differently at the threshold the rows happen to leave it at need not do that.
 *
 * <p>The rows leave a range of thresholds on a line beside the border: past every row the model
 * keeps and short of every row it refuses. A row the model keeps that lands inside that range is
 * answered differently by the line drawn at the near end — and is kept by the same line drawn at the
 * row itself, which still refuses every row the model refuses. Counted as settling, the block would
 * offer that row, the author would write it, and the next run would find the same line standing a
 * step further along.
 *
 * <p>So the question a row is put ({@link AnotherLineTheRowsAllow.Stands#ruledOutBy}) is held here
 * to the measurement's own answer over the rows with that row added: one rule, asked by the
 * generation and by the measurement, and this is what keeps the two from drifting apart.
 */
class ARowThatOnlyMovesTheThresholdLeavesTheLineStandingTest {

    /**
     * Rows over {@code -2 * x + y <= 0} that leave {@code -3 * x + y} standing with room inside the
     * range: along it the rows the model keeps reach {@code 0} at {@code (0, 0)}, and the one it
     * refuses is at {@code 5}.
     */
    private static final int[][] KEPT_BELOW = {{0, 0}, {0, 5}, {13, 23}, {12, 24}};

    /**
     * The same over {@code -2 * x + y >= 0}, where further along runs the other way: the rows the
     * model keeps reach down to {@code 0} and the nearest it refuses is at {@code -2}.
     */
    private static final int[][] KEPT_ABOVE = {{0, 0}, {0, 3}, {0, -5}, {1, 1}};

    /** The line of the family both sets of rows leave standing. */
    private static final String WEIGHING_X_ONE_MORE = "-3 * x + y";

    @Test
    void aKeptRowInsideTheRangeIsAnsweredDifferentlyAtTheThresholdAndRulesNothingOut() {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();
        AnotherLineTheRowsAllow.Stands before = standing(border, KEPT_BELOW);
        assertEquals(ExactRatio.ZERO, before.cut(), () -> "the near end: " + before);
        assertEquals(ExactRatio.of(5), before.refusedFrom(), () -> "and the far one: " + before);

        // Kept by the model, and one step past the near end along the line beside it.
        Map<NumericTerm, Place> inside = at(border, -1, -2);
        assertTrue(keeps(drawn(border), inside), "the model keeps it");

        assertEquals(ExactAnswer.held(false), before.ruledOutBy(drawn(border), inside),
                () -> "a kept row inside the range does not rule the line out: " + inside);
        // And the measurement says the same with the row written: the line still stands, at the
        // row it was moved to, as the same obligation.
        AnotherLineTheRowsAllow.Stands after = assertInstanceOf(
                AnotherLineTheRowsAllow.Stands.class, line(border, with(border, KEPT_BELOW, inside)),
                "the line survives the row");
        assertEquals(ExactRatio.ONE, after.cut(), "and stands at the threshold the row moved it to");
        assertEquals(before.direction(), after.direction(), "which is the same obligation");
    }

    @Test
    void aKeptRowAtTheFarEndRulesTheLineOut() {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();
        AnotherLineTheRowsAllow.Stands before = standing(border, KEPT_BELOW);

        // Kept by the model and at 5 along the line beside it, which is where the refused row is.
        Map<NumericTerm, Place> atTheFarEnd = at(border, -5, -10);
        assertTrue(keeps(drawn(border), atTheFarEnd), "the model keeps it");
        assertEquals(ExactAnswer.held(true), before.ruledOutBy(drawn(border), atTheFarEnd),
                () -> "no threshold keeps it and refuses the row at the same place: " + atTheFarEnd);
        assertInstanceOf(AnotherLineTheRowsAllow.RuledOut.class,
                line(border, with(border, KEPT_BELOW, atTheFarEnd)),
                "and the measurement rules the line out with the row written");
    }

    /**
     * A row whose sum along the line the exact arithmetic cannot hold leaves the line undecided,
     * and never ruled out.
     *
     * <p>A tenth to a power near the end of the range, beside a whole one: weighed and added, no
     * number the arithmetic holds. Read as no threshold found, the line was gone from the family's
     * answer — counted as told apart on the strength of a sum nobody worked out.
     */
    @Test
    void aRowTheArithmeticCannotHoldLeavesTheLineUndecided() {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();
        List<Map<NumericTerm, Place>> rows = new ArrayList<>(rowsOf(border, KEPT_BELOW));
        Map<NumericTerm, Place> unheld = at(border, 0, 1);
        unheld.replaceAll((term, place) -> term.equals(unheld.keySet().iterator().next())
                ? Count.of(new BigDecimal(BigInteger.ONE, 1 << 30)) : place);
        rows.add(unheld);

        AnotherLineTheRowsAllow.Undecided open = assertInstanceOf(
                AnotherLineTheRowsAllow.Undecided.class, line(border, rows),
                "the row could have been the one that rules it out, or not");
        assertTrue(aRowNotWorkedOut(open), () -> "and what stopped it is a row whose number the"
                + " arithmetic could not hold, in the words a reading answers in: " + open);
    }

    /**
     * A row whose sum on the model's own line the arithmetic cannot hold is on neither side of it,
     * and so rules no line out — however well its sum along the line beside it is held.
     *
     * <p>{@code -x} is the line of the family weighing {@code y} one less, so it reads nothing of
     * {@code y}. The rows leave it standing: along it the rows the model keeps reach {@code 0} and
     * the one it refuses is at {@code 1}. The row added holds a tenth to a power near the end of
     * the range at {@code y}: the model keeps it, since {@code -2 + y} is below nought, and no sum
     * the arithmetic holds says so. Along {@code -x} it is at {@code -1}, within reach of the rows
     * the model keeps — so read as refused, as a yes-or-no reading of the model's side reads a sum
     * it cannot hold, it would rule the line out.
     */
    @Test
    void aRowWhoseSideOfTheModelsLineCannotBeHeldRulesNothingOut() {
        Border border = TheLinesBesideABorder.aLineOverTwoPositions();
        int[][] rows = {{0, 0}, {2, 4}, {-1, 5}};
        AnotherLineTheRowsAllow.Direction before = line(border, rowsOf(border, rows), "-x");
        AnotherLineTheRowsAllow.Stands standing = assertInstanceOf(
                AnotherLineTheRowsAllow.Stands.class, before, "the rows leave -x standing");

        Map<NumericTerm, Place> unplaced = at(border, 1, 0);
        unplaced.replaceAll((term, place) -> term.toString().equals(lastTerm(border))
                ? Count.of(new BigDecimal(BigInteger.ONE, 1 << 30)) : place);
        assertInstanceOf(ExactAnswer.Unheld.class, drawn(border).satisfies(unplaced),
                "which side of the model's line it is on is not held");

        assertInstanceOf(ExactAnswer.Unheld.class, standing.ruledOutBy(drawn(border), unplaced),
                "an offered row this cannot place is not said to rule the line out");
        AnotherLineTheRowsAllow.Undecided after = assertInstanceOf(
                AnotherLineTheRowsAllow.Undecided.class,
                line(border, with(border, rows, unplaced), "-x"),
                "and with it written the line is undecided, not ruled out");
        assertTrue(aRowNotWorkedOut(after), () -> "for the arithmetic on that row: " + after);
    }

    /** Whether a line was left undecided by a row read in part because its number was not held. */
    private static boolean aRowNotWorkedOut(AnotherLineTheRowsAllow.Undecided line) {
        return line.why() instanceof AnotherLineTheRowsAllow.Unsettled.RowsIncomplete(var met)
                && met.eachKindOnce().written().stream()
                        .anyMatch(ReadingGap.CouldNotWorkOut.class::isInstance);
    }

    /** One rule, asked by the generation and by the measurement, on either side the line keeps. */
    @Test
    void whatRulesTheLineOutIsWhatTheMeasurementSaysOfTheRowsWithItWritten() {
        agreeOverAGrid(TheLinesBesideABorder.aLineOverTwoPositions(), KEPT_BELOW);
        agreeOverAGrid(TheLinesBesideABorder.aLineOverTwoPositionsKeptAbove(), KEPT_ABOVE);
    }

    private static void agreeOverAGrid(Border border, int[][] rows) {
        AnotherLineTheRowsAllow.Stands before = standing(border, rows);
        OrderedAffineBoundary drawn = drawn(border);
        int ruledOut = 0;
        int keptAndLeftStanding = 0;
        for (int x = -8; x <= 16; x++) {
            for (int y = -16; y <= 30; y++) {
                Map<NumericTerm, Place> candidate = at(border, x, y);
                boolean kept = keeps(drawn, candidate);
                boolean says = before.ruledOutBy(drawn, candidate).orFail("a whole row's sums");
                boolean measured = line(border, with(border, rows, candidate))
                        instanceof AnotherLineTheRowsAllow.RuledOut;
                assertEquals(measured, says, () -> "at " + candidate + " beside " + before);
                if (says) {
                    ruledOut++;
                } else if (kept) {
                    keptAndLeftStanding++;
                }
            }
        }
        // Both answers are given over the grid, and among the rows that leave the line standing
        // are ones the model keeps, so the agreement is about the case this test is for.
        int ruled = ruledOut;
        int left = keptAndLeftStanding;
        assertTrue(ruled > 0 && left > 0,
                () -> "the grid holds rows of both kinds beside " + before + ": " + ruled
                        + " ruling it out and " + left + " kept rows that do not");
    }

    private static AnotherLineTheRowsAllow.Stands standing(Border border, int[][] rows) {
        return assertInstanceOf(AnotherLineTheRowsAllow.Stands.class,
                line(border, rowsOf(border, rows)),
                "the rows leave the line standing");
    }

    /** What the measurement says about the line of the family weighing {@code x} one more. */
    private static AnotherLineTheRowsAllow.Direction line(Border border,
                                                          List<Map<NumericTerm, Place>> rows) {
        return line(border, rows, WEIGHING_X_ONE_MORE);
    }

    /** What the measurement says about the line of the family spelled {@code spelled}. */
    private static AnotherLineTheRowsAllow.Direction line(Border border,
                                                          List<Map<NumericTerm, Place>> rows,
                                                          String spelled) {
        AnotherLineTheRowsAllow said = AnotherLineTheRowsAllow.of(List.of(
                new AnotherLineTheRowsAllow.Reading(border,
                        () -> new StandingAtAPoint.RowsRead(rows, Set.of(),
                                StandingAtAPoint.ReadingsTried.EVERY_ONE, false),
                        List.of(), WayToTheBorder.UNTOUCHED, _ -> false)), true);
        for (AnotherLineTheRowsAllow.Direction each : assertInstanceOf(
                AnotherLineTheRowsAllow.ByDirection.class, said).each()) {
            if (OrderedAffineBoundary.spelled(each.direction().direction()).equals(spelled)) {
                return each;
            }
        }
        throw new AssertionError(spelled + " is a line of the family: " + said);
    }

    private static OrderedAffineBoundary drawn(Border border) {
        return OrderedAffineBoundary.of(border).orFail("a line worked out").orElseThrow();
    }

    /** Whether the model's line is shown to keep a row. */
    private static boolean keeps(OrderedAffineBoundary drawn, Map<NumericTerm, Place> row) {
        return Boolean.TRUE.equals(drawn.satisfies(row).orNull());
    }

    /** The name of the second of the two terms the line is over, which is {@code y}. */
    private static String lastTerm(Border border) {
        List<NumericTerm> terms = new ArrayList<>(
                ((LinearQuantity) border.cut().of()).direction().coefs().keySet());
        terms.sort(Comparator.comparing(NumericTerm::toString));
        return terms.get(1).toString();
    }

    private static List<Map<NumericTerm, Place>> with(Border border, int[][] rows,
                                                      Map<NumericTerm, Place> one) {
        List<Map<NumericTerm, Place>> out = new ArrayList<>(rowsOf(border, rows));
        out.add(one);
        return out;
    }

    private static List<Map<NumericTerm, Place>> rowsOf(Border border, int[][] rows) {
        List<Map<NumericTerm, Place>> out = new ArrayList<>();
        for (int[] row : rows) {
            out.add(at(border, row[0], row[1]));
        }
        return out;
    }

    /** One reading, each value on the term the quantity reads it at, {@code x} before {@code y}. */
    private static Map<NumericTerm, Place> at(Border border, int x, int y) {
        List<NumericTerm> terms = new ArrayList<>(
                ((LinearQuantity) border.cut().of()).direction().coefs().keySet());
        terms.sort(Comparator.comparing(NumericTerm::toString));
        Map<NumericTerm, Place> at = new LinkedHashMap<>();
        at.put(terms.get(0), Count.of(x));
        at.put(terms.get(1), Count.of(y));
        return at;
    }
}
