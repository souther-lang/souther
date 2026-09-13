package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point asked for one value after another is answered by what was built, and never by the last
 * asking having nothing left to build.
 *
 * <p>A place the region admits is less than the question a point asks: the row built there may turn
 * back above the line and never arrive. So a value that composed a row which did not stand is put
 * aside and the point is asked for another — and each asking after the first is a smaller question,
 * because a value the point may not use again is a value there is no longer.
 *
 * <p><b>Which is why the first answer is the point's.</b> A later asking that reaches nothing has
 * reached nothing of the smaller question, and it is the one that runs out. Read as the point's own
 * answer, a row that was composed and did not stand comes back as a row nothing could build — the
 * one thing this must not say of a point it built a value for.
 *
 * <p>And running out is not a proof either way: neither the values of a position nor a figure of
 * this compiler's reaching its end says a row cannot be written there.
 */
class APointTriedWithSeveralValuesIsAnsweredByWhatWasBuiltTest {

    /**
     * A line over two positions with a handful of values between them, none of whose rows arrive.
     *
     * <p>The condition above the line is about a number made from the position, so the row is
     * composed without it — and it holds of nothing the positions admit, so every row turns back
     * there. The pairs the rule leaves are few, so the asking runs out of them before the figure
     * runs out of askings, which is what puts the last word in the mouth of a search that had
     * nothing left to look for.
     */
    private static final String THE_VALUES_RUN_OUT = """
            module example.few

            data Bit = Int
                invariant range = value >= 0 && value <= 2

            data Yes = { v: Int }
            data No = { why: Int }

            behavior f : (x: Bit, y: Bit) -> Yes | No
                constructs Yes
                constructs No

            let f (x, y) = {
                guard Int.abs(x.value) > 100 else No { why = 0 }
                guard x.value < y.value else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    /**
     * And a line whose positions never run out, so the figure is what ends the asking.
     *
     * <p>The condition on the length is one the row is composed without — it is a second number of
     * a location the comparison already writes — and nothing offered for {@code b} meets it: the
     * only string of no characters is the least one there is, so no value stands below it. Every
     * value the point is tried with builds a row, and every row turns back at the guard.
     */
    private static final String EVERY_ROW_TURNS_BACK = """
            module example.spent

            data Yes = { v: Int }
            data No = { why: Int }

            behavior cmp : (a: String, b: String) -> Yes | No
                constructs Yes
                constructs No

            let cmp (a, b) = {
                guard String.length(b) < 1 else No { why = 0 }
                guard a < b else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    @Test
    void whatWasBuiltIsWhatTheReaderIsTold() {
        List<String> said = whereNothingCouldShowARow(THE_VALUES_RUN_OUT);

        assertFalse(said.isEmpty(), "this model has points nothing established a row at");
        for (String each : said) {
            assertTrue(each.contains("was seen reaching it"),
                    () -> "rows were composed for this point and none of them arrived: " + each);
            assertFalse(each.contains("nothing here could build a representative"),
                    () -> "and it is not answered as a point nothing composed a row for: " + each);
        }
    }

    @Test
    void andRunningOutOfValuesIsNotAProof() {
        for (String model : List.of(THE_VALUES_RUN_OUT, EVERY_ROW_TURNS_BACK)) {
            List<String> said = whereNothingCouldShowARow(model);

            assertFalse(said.isEmpty(), () -> "this model has points nothing established a row at:\n"
                    + model);
            for (String each : said) {
                assertTrue(each.contains("which does not make it unreachable"),
                        () -> "a point this stopped asking about is not one nothing can stand at: "
                                + each);
            }
        }
    }

    /**
     * And the figure that ended the asking is what a reader is told about.
     *
     * <p>The point is open because this compiler stopped putting values to it, which is a number
     * somebody could raise. Left off, the page says a search had everything and reached nothing,
     * and the one thing an author could do about it is not on it.
     */
    @Test
    void andTheFigureThatEndedTheAskingIsSaid() {
        List<String> said = whereNothingCouldShowARow(EVERY_ROW_TURNS_BACK);

        assertFalse(said.isEmpty(), "this model has points nothing established a row at");
        for (String each : said) {
            assertTrue(each.contains("how many values a point is tried with"),
                    () -> "the figure the asking stopped at is on the line: " + each);
        }
    }

    /**
     * And a point whose values ran out says no such thing.
     *
     * <p>The control. Nothing of this compiler's ended that asking — the positions had no further
     * value to stand at — so a figure said there would be a number an author could raise to be
     * told exactly the same thing.
     */
    @Test
    void andAPointWhoseValuesRanOutNamesNoFigure() {
        List<String> said = whereNothingCouldShowARow(THE_VALUES_RUN_OUT);

        assertFalse(said.isEmpty(), "this model has points nothing established a row at");
        for (String each : said) {
            assertFalse(each.contains("how many values a point is tried with"),
                    () -> "the values ran out before the figure did: " + each);
        }
    }

    /** The point lines of the page that say a search came to nothing. */
    private static List<String> whereNothingCouldShowARow(String model) {
        List<String> found = new ArrayList<>();
        for (String line : human(model).split("\n")) {
            if (line.contains("nothing composed one") || line.contains("over less than the point")) {
                found.add(line.trim());
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
