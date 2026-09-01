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
 * A point whose count no value of the order stands at is a point nothing composes a value for.
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
 * <p>What such a point leaves is what a point nothing can be written at has always left, and the
 * border beside it is unaffected — the line is still drawn, and the points that do have values keep
 * them.
 */
class ACountNoValueOfTheOrderStandsAtComposesNothingTest {

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
     * The point below it composes nothing, and says so.
     *
     * <p>The band this line leaves has its points at nought and beside it, and a time of day at the
     * bottom of its order has nothing below it: the point wants a second before midnight of the
     * first day there is. So it is unresolved for the reason a point nothing can be written at is
     * unresolved, which is the answer that was already there for a case no module can name.
     */
    @Test
    void thePointBelowItIsUnresolvedRatherThanThrown() {
        List<String> reasons = new ArrayList<>();
        for (BorderAssessment border : measured()) {
            border.items().forEach((role, item) -> {
                if (item instanceof ItemAssessment.Owed owed
                        && owed.searches().only() instanceof ItemAssessment.Attempt.Unresolved unresolved) {
                    reasons.add(unresolved.why().reason().toString());
                }
            });
        }
        assertTrue(!reasons.isEmpty(), "a point of this line was owed a row and got none");
        assertEquals(List.of(), reasons.stream()
                        .filter(each -> !each.equals("NOTHING_COMPOSES_ONE")).toList(),
                "and that is what a point nothing composes a value at says: " + reasons);
    }

    /** And the points that do have values keep them, so the line was not emptied to get here. */
    @Test
    void thePointsWithValuesKeepThem() {
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
        assertEquals(List.of(
                        "[Date(\"1970-01-01\"), Time(\"00:00:00\"), DateTime(\"1970-01-01T00:00:00\")]",
                        "[Date(\"1970-01-01\"), Time(\"00:00:01\"), DateTime(\"1970-01-01T00:00:00\")]"),
                rows,
                "the two points that have a value, at the counts the declared form puts them at");
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
