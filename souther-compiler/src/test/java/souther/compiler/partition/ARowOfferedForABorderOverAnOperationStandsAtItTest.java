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
        PartitionEvidence measured = measured(SPAN);

        assertEquals(List.of("b - 10"), measured.boundaries().stream()
                .map(BorderAssessment::value).filter(each -> each.contains("b")).toList(),
                "the line `Date.daysBetween(a, b) > 10` draws");
        assertTrue(!open(measured).isEmpty(),
                "and points of it nothing has covered, for a row to be offered at");
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
        Map<String, String> rows = offeredAt(measured(SPAN));

        PartitionEvidence again = measured(SPAN + "\nexample f\n"
                + String.join("\n", rows.values()) + "\n");

        assertEquals(List.of(), open(again).stream().filter(rows::containsKey).toList(),
                "each point a row was offered at was met once that row was in: " + rows);
    }

    /** The points of every border a row is owed at and nothing stands at. */
    private static List<String> open(PartitionEvidence evidence) {
        List<String> points = new ArrayList<>();
        for (BorderAssessment border : evidence.boundaries()) {
            border.items().forEach((role, item) -> {
                if (item instanceof ItemAssessment.Owed owed
                        && !ItemAssessment.Coverage.hit(owed.coverage())) {
                    points.add(border.label() + " " + role);
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
    private static Map<String, String> offeredAt(PartitionEvidence evidence) {
        Map<String, String> rows = new LinkedHashMap<>();
        for (BorderAssessment border : evidence.boundaries()) {
            border.items().forEach((role, item) -> {
                if (item instanceof ItemAssessment.Owed owed
                        && owed.attempt() instanceof ItemAssessment.Attempt.Built built) {
                    rows.put(border.label() + " " + role, written(built.row()));
                }
            });
        }
        return rows;
    }

    /** A built row as an example line, answered the way the behavior answers it. */
    private static String written(Generator.GeneratedRow row) {
        List<String> inputs = row.inputs().stream().map(FixtureTemplate::text).toList();
        List<LocalDate> dates = new ArrayList<>();
        for (String each : inputs) {
            Matcher found = WRITTEN_DATE.matcher(each);
            dates.add(found.find() ? LocalDate.parse(found.group(1)) : null);
        }
        String answers = dates.size() == 2 && dates.get(0) != null && dates.get(1) != null
                && ChronoUnit.DAYS.between(dates.get(0), dates.get(1)) > 10 ? "Ok" : "No";
        return "    | (" + String.join(", ", inputs) + ") -> " + answers;
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
}
