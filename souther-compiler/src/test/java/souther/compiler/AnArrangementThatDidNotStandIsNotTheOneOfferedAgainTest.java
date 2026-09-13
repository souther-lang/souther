package souther.compiler;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point whose first arrangement did not stand is asked for another, whichever search composed it.
 *
 * <p>Three shapes answer a point — one position at a place of its own, a pair on one line, and
 * every position of a form at values that add up — and a value put aside has to reach all of them.
 * Reaching two, the third hands back the arrangement it handed back before: the search runs its
 * whole allowance of values over one of them, and a point it had a row for goes out open.
 *
 * <p><b>A whole arrangement and not a place of it.</b> What the form's walk chooses is every
 * position at once, so what it may not hand back again is that — and every arrangement standing one
 * of those positions where this one stood it is still one nothing has tried.
 */
class AnArrangementThatDidNotStandIsNotTheOneOfferedAgainTest {

    /**
     * A line over a form, above a condition the walk cannot represent.
     *
     * <p>The comparison puts a date, a time of day and a date-time on one order, which is a form
     * over three positions. Above it stands an outcome that states one of two things — the walk has
     * no cut for it, so the row is composed without it — and the arrangement the arithmetic reaches
     * first is the one it refuses: the day the dates start at, at the second the times start at. A
     * day or a second further on and the row arrives.
     */
    private static final String A_FORM_UNDER_A_CONDITION_NOTHING_PLACED = """
            module demo

            data Ok
            data No

            behavior f : (d: Date, t: Time, b: DateTime) -> Ok | No
            let f (d, t, b) = {
                guard d > Date("1970-01-01") || t > Time("00:00:00") else No
                guard b > DateTime.fromDateAndTime(d, t) else No
                Ok
            }
            """;

    @Test
    @DisplayName("a point of the form's line is answered by the arrangement after the one that failed")
    void thePointOfAFormIsAnsweredByALaterArrangement() {
        List<String> open = whatNothingCouldShow(A_FORM_UNDER_A_CONDITION_NOTHING_PLACED);

        assertEquals(List.of(), open.stream()
                        .filter(each -> each.contains("b - 86400 * d - t = 1")
                                || each.contains("1 < b - 86400 * d - t"))
                        .toList(),
                "a row stands at these once the arrangement that did not stand is put aside");
    }

    @Test
    @DisplayName("and the model is one whose first arrangement does not stand")
    void andTheFirstArrangementIsOneThatDoesNotStand() {
        String page = human(A_FORM_UNDER_A_CONDITION_NOTHING_PLACED);

        assertTrue(page.contains("an outcome that states one of two things"),
                () -> "the row is composed without the condition above the line: " + page);
    }

    /** The points of the page that no search established a row at. */
    private static List<String> whatNothingCouldShow(String model) {
        List<String> found = new ArrayList<>();
        for (String line : human(model).split("\n")) {
            if (line.contains("nothing could show a row can be written at")
                    || line.contains("nothing composed one")
                    || line.contains("over less than the point had")) {
                found.add(line.strip());
            }
        }
        return found;
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
