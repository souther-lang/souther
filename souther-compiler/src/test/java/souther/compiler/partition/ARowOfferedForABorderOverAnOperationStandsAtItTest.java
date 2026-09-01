package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;

import java.time.LocalDate;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row offered at a point of a border stands at the point it was offered for.
 *
 * <p>A border being drawn is one thing and a row for it being writable is another. What must hold is
 * the round trip: a row offered for a point, put back into the model and measured again, is at that
 * point. A row offered for one point and standing at another sends an author to write something that
 * answers a question it was not written for, and the report would say the point was covered.
 *
 * <p><b>How many rows there are is not asked.</b> Whether the search reaches an assignment is its
 * own answer and moves with what a model leaves each position — a point nothing could be composed
 * for is a point with no row here, which is a fact about the search rather than a broken promise.
 * So the rows are taken as offered and each is held to its own point, and none of it says there
 * must be any.
 *
 * <p>What <em>is</em> asked is that the border this is about is here with points still open. Without
 * it the round trip is over nothing and passes quietly, which is how the first version of this test
 * passed while comparing one empty list to another.
 */
class ARowOfferedForABorderOverAnOperationStandsAtItTest {

    private static final String SPAN = """
            module demo

            data Ok
            data No
            data Day = Date
                invariant value >= Date("2000-01-01")
                invariant value <= Date("2030-12-31")

            behavior f : (a: Day, b: Day) -> Ok | No
            let f (a, b) = {
                guard Date.daysBetween(a.value, b.value) > 10 else No
                Ok
            }
            """;

    /** {@code Day(Date("2000-01-01"))}, as a row's input is written. */
    private static final Pattern WRITTEN_DATE = Pattern.compile("Date\\(\"([0-9-]+)\"\\)");

    /**
     * The border the operation draws is here, and its points are open.
     *
     * <p>The guard on everything below. A model whose border went away, or whose points were all
     * covered by something else, would leave the round trip with nothing to make and nothing to say.
     */
    @Test
    void theBorderThisIsAboutIsDrawnAndItsPointsAreOpen() {
        List<BorderAssessment> lines = lines(SPAN);

        assertEquals(List.of("b - 10"), lines.stream()
                .map(BorderAssessment::value).filter(each -> each.contains("b")).toList(),
                "the line `Date.daysBetween(a, b) > 10` draws");
        assertTrue(!open(lines).isEmpty(),
                "and points of it nothing has covered, for a row to be offered at");
    }

    /**
     * A row is offered at each of that border's own points.
     *
     * <p>What the round trip below is over. It holds every row offered to its own point and says
     * nothing about there being any, so it passed while this border offered none at all and the only
     * rows going round were the ones for the lines through each date's own values (#1018).
     *
     * <p>Which is not the general promise that a point has a row — a point nothing composes for is
     * an answer the search is entitled to give. It is this border, over an operation whose positions
     * are written back differently from what it answers, and the four points it draws.
     */
    @Test
    void thePointsOfThatBorderAreOfferedRows() {
        Map<String, String> rows = offeredAt(lines(SPAN));

        assertEquals(List.of("a = b - 10 ON", "a = b - 10 OFF", "a = b - 10 IN", "a = b - 10 OUT"),
                rows.keySet().stream().filter(each -> each.startsWith("a = b - 10 ")).toList(),
                "each point of `Date.daysBetween(a, b) > 10` has a row: " + rows);
    }

    /**
     * A distance between two positions written back differently, which is the other lowering.
     *
     * <p>{@code a} is a whole number and {@code b} a decimal, so the two are one distance on two
     * orders — the pair the search for a distance on one order was never written for, and the pair
     * {@link BorderQuantity.Apart} hands to the search over forms instead.
     */
    private static final String ACROSS_TWO_ORDERS = """
            module demo

            data Ok
            data No

            behavior f : (a: Int, b: Decimal) -> Ok | No
            let f (a, b) = {
                guard b > Decimal.fromInt(a) else No
                Ok
            }
            """;

    /**
     * The points of that border are offered rows too, each position written on its own order.
     *
     * <p><b>Asked for the rows and not only for their soundness.</b> Every other test of this
     * lowering holds a row that was offered to what it must be, and passes when none was: the branch
     * could stop composing anything and each of them would go on saying nothing. So the rows are
     * asked for here, where an empty answer is the failure.
     *
     * <p>And asked for the spelling, which is the defect itself. Both positions were written on
     * whichever order the comparison happened to answer with, so an {@code Int} was offered
     * {@code 0m} — a row the report counted and the compiler will not read.
     */
    @Test
    void thePointsOfABorderAcrossTwoOrdersAreOfferedRowsWrittenOnEachOrder() {
        Map<String, String> rows = inputsOf(lines(ACROSS_TWO_ORDERS));

        assertEquals(List.of("b = a OFF", "b = a IN", "b = a OUT"),
                rows.keySet().stream().filter(each -> each.startsWith("b = a ")).toList(),
                "each point of `b > Decimal.fromInt(a)` that is owed a row has one: " + rows);
        assertEquals(List.of("(0, 0m)", "(0, 1m)", "(0, -1m)"),
                rows.entrySet().stream().filter(each -> each.getKey().startsWith("b = a "))
                        .map(Map.Entry::getValue).toList(),
                "and the whole number is written as one and the decimal as one: " + rows);
    }

    /**
     * The same two orders, where the run one of them leaves has no value the other holds in it.
     *
     * <p>{@code b} runs between three tenths and seven tenths, so the line holds {@code a} between
     * minus two tenths and two tenths — a run with one whole number in it and every decimal around
     * that one.
     */
    private static final String A_RUN_ONE_ORDER_FILLS = """
            module demo

            data Ok
            data No
            data Amount = Decimal
                invariant value >= 0.3m
                invariant value <= 0.7m

            behavior f : (a: Int, b: Amount) -> Ok | No
            let f (a, b) = {
                guard b.value > Decimal.fromInt(a) + 0.5m else No
                Ok
            }
            """;

    /**
     * And the pair is searched for on both orders, not on whichever one of them the line was named
     * by.
     *
     * <p><b>The test that fails if the lowering goes away.</b> The one above passes on either
     * search: the run it leaves has whole numbers in it wherever a walk starts, so a search that
     * walked the decimals landed on one anyway. Here it does not — the whole numbers are one value
     * in a run the decimals fill — and a search holding both positions to the decimals hands the
     * whole number three tenths, which is not a rounding error but a value of a type it is not.
     *
     * <p>Measured rather than argued: with both positions on the decimals this model does not come
     * back with a worse row, it comes back with {@code ArithmeticException: Rounding necessary} out
     * of the writing of the row.
     */
    @Test
    void andThePairIsSearchedForOnBothOrders() {
        Map<String, String> rows = inputsOf(lines(A_RUN_ONE_ORDER_FILLS));

        assertEquals("(0, Amount(0.5m))", rows.get("b = a + 0.5 OFF"),
                "the point on the line has the one whole number the line leaves, and the decimal"
                        + " half a step above it: " + rows);
    }

    /**
     * And every row offered at a point stands at that point.
     *
     * <p>Read off the point's own attempt rather than out of the block a report prints: the row a
     * point was composed for is the one recorded against it, and matching them up again by parsing
     * text would be a second answer to a question already answered.
     */
    @Test
    void everyRowOfferedAtAPointStandsAtIt() {
        Map<String, String> rows = offeredAt(lines(SPAN));

        List<BorderAssessment> again = lines(SPAN + "\nexample f\n"
                + String.join("\n", rows.values()) + "\n");

        assertEquals(List.of(), open(again).stream().filter(rows::containsKey).toList(),
                "each point a row was offered at was met once that row was in: " + rows);
    }

    /** The points of every border a row is owed at and nothing stands at. */
    private static List<String> open(List<BorderAssessment> lines) {
        List<String> points = new ArrayList<>();
        for (BorderAssessment border : lines) {
            border.items().forEach((role, item) -> {
                if (item instanceof ItemAssessment.Owed owed
                        && !owed.hasRowWitness()) {
                    points.add(border.label() + " " + border.border().named(role));
                }
            });
        }
        return points;
    }

    /**
     * The row offered at each point that has one, by the point it was offered at.
     *
     * <p>Empty where the search composed nothing, which is what a point with no row is. Whether that
     * happens is the search's answer and no part of what this holds.
     */
    private static Map<String, String> offeredAt(List<BorderAssessment> lines) {
        return offeredAt(lines, ARowOfferedForABorderOverAnOperationStandsAtItTest::written);
    }

    /** The same, as each row's inputs alone — for a model whose rows are not written as dates and
     *  whose answer nothing here works out. */
    private static Map<String, String> inputsOf(List<BorderAssessment> lines) {
        return offeredAt(lines, row -> "("
                + String.join(", ", row.inputs().stream().map(FixtureTemplate::text).toList()) + ")");
    }

    private static Map<String, String> offeredAt(
            List<BorderAssessment> lines,
            java.util.function.Function<Generator.GeneratedRow, String> as) {
        Map<String, String> rows = new LinkedHashMap<>();
        for (BorderAssessment border : lines) {
            border.items().forEach((role, item) -> {
                if (item instanceof ItemAssessment.Owed owed
                        && owed.searches().only() instanceof ItemAssessment.Attempt.Built built) {
                    rows.put(border.label() + " " + border.border().named(role),
                            as.apply(built.row()));
                }
            });
        }
        return rows;
    }

    /**
     * A built row as an example line, answered the way {@link #SPAN}'s guard answers it.
     *
     * <p>The answer is worked out here because a row is offered with its result left for an author
     * to fill in, and the round trip needs it filled. That makes this the fixture's guard written a
     * second time, and the two have to move together — which is why it is the guard of a model
     * three lines long rather than of anything a reader would have to think about.
     *
     * <p>A row that is not two written dates is refused rather than answered {@code No}. What a row
     * looks like is the generator's to decide, and guessing at one this does not recognise would
     * fill every point with the same answer and call the round trip green.
     */
    private static String written(Generator.GeneratedRow row) {
        List<String> inputs = row.inputs().stream().map(FixtureTemplate::text).toList();
        List<LocalDate> dates = new ArrayList<>();
        for (String each : inputs) {
            Matcher found = WRITTEN_DATE.matcher(each);
            assertTrue(found.find(), () -> "a row of this behavior is written as two dates: " + each);
            dates.add(LocalDate.parse(found.group(1)));
        }
        assertEquals(2, dates.size(), () -> "and there are two of them: " + inputs);
        return "    | (" + String.join(", ", inputs) + ") -> "
                + (ChronoUnit.DAYS.between(dates.get(0), dates.get(1)) > 10 ? "Ok" : "No");
    }

    private static PartitionEvidence measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + source);
        PartitionEvidence measured = coverage.get("f");
        assertNotNull(measured, () -> "f was measured: " + source);
        return measured;
    }

    /** The lines the behavior's positions met, whosever the row at each point is. */
    private static List<BorderAssessment> lines(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> read =
                Adequacy.readingsOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(read, () -> "the model under test compiles: " + source);
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, () -> "f was measured: " + source);
        return lines;
    }
}
