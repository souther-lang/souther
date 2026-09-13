package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point whose count one position of a form cannot stand at is reached by the rest of them.
 *
 * <p>An order that counts may stop. A time of day counts seconds from midnight and has 86400 of
 * them, so the count below its first is a count no time has — and the arithmetic that puts a point
 * beside a line knows nothing of that, since a count is a number and the ends are the order's.
 * Written out regardless, the conversion refused it the only way it could: {@code Time} came back
 * from {@code LocalTime.ofSecondOfDay(-1)} as a {@code DateTimeException}, out of the middle of a
 * measurement, on a model that compiles.
 *
 * <p>Reached through {@code DateTime.fromDateAndTime}, which is what first puts a time of day where
 * a line is drawn: a date-time counts seconds and is a day count and a second of one put together,
 * so a rule over it has a position on the bounded order. Every other order a line had been drawn on
 * stops nowhere a count reaches.
 *
 * <p>What the point wants is a count and not a time of day, and a form has more than one position
 * to reach a count with: the second before the first midnight is the last second of the day before.
 * So the answer is a row at that day, and never a time the order has no value for — which is the
 * thing that threw, and is what the walk still may not write.
 */
class ACountNoValueOfTheOrderStandsAtIsReachedAnotherWayTest {

    private static final String MODEL = """
            module demo

            data Ok
            data No

            behavior f : (d: Date, t: Time, b: DateTime) -> Ok | No
            let f (d, t, b) = {
                guard b > DateTime.fromDateAndTime(d, t) else No
                Ok
            }
            """;

    /** The line is drawn, over the counts the operation was declared with. */
    @Test
    void theLineIsStillDrawn() {
        assertEquals(List.of("b - 86400 * d - t = 0"), measured().stream()
                .map(BorderAssessment::label).toList());
    }

    /**
     * The point below it is answered by the day before, and never by a time before midnight.
     *
     * <p>The band this line leaves has its points at nought and beside it, and a time of day at the
     * bottom of its order has nothing below it: read as a time, the point wants a second before
     * midnight of the first day there is. Read as a count of the form, it wants what the last
     * second of the day before adds up to — which is a row, and the one the walk hands back once
     * the arrangement it reached first is put aside.
     */
    @Test
    void thePointBelowItIsReachedByTheDayBefore() {
        assertTrue(rowsComposed().contains(
                        "[Date(\"1969-12-31\"), Time(\"23:59:59\"),"
                                + " DateTime(\"1970-01-01T00:00:00\")]"),
                () -> "the count below the first midnight is a day earlier: " + rowsComposed());
    }

    /** And every one of them is a value the orders hold, which is what threw. */
    @Test
    void everyRowIsOneTheOrdersHold() {
        assertEquals(List.of(
                        "[Date(\"1969-12-31\"), Time(\"23:59:59\"),"
                                + " DateTime(\"1970-01-01T00:00:00\")]",
                        "[Date(\"1970-01-01\"), Time(\"00:00:00\"),"
                                + " DateTime(\"1970-01-01T00:00:00\")]",
                        "[Date(\"1969-12-31\"), Time(\"23:59:58\"),"
                                + " DateTime(\"1970-01-01T00:00:00\")]",
                        "[Date(\"1970-01-01\"), Time(\"00:00:01\"),"
                                + " DateTime(\"1970-01-01T00:00:00\")]"),
                rowsComposed(),
                "the points of this line, at counts the declared form puts them at");
    }

    /** What each point of the line was given, in the order the points are held. */
    private static List<String> rowsComposed() {
        List<String> rows = new ArrayList<>();
        for (BorderAssessment border : measured()) {
            border.items().forEach((role, item) -> {
                if (item instanceof ItemAssessment.Owed owed
                        && owed.searches().only() instanceof ItemAssessment.Attempt.Built built) {
                    rows.add(built.row().inputs().stream().map(FixtureTemplate::text).toList()
                            .toString());
                }
            });
        }
        return rows;
    }

    /** The lines the behavior's positions met, whosever the row at each point is. */
    private static List<BorderAssessment> measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> read =
                Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }
}
