package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total over a list the body writes out is read as the sum of its elements, as the size of the
 * same list is read as how many were written.
 *
 * <p>Asked of the report a person reads: the total written over the list gives the report the sum
 * of the elements written out gives, wherever in the guard each is written.
 */
class ATotalOverAListTheBodyWritesOutIsReadTest {

    private static final String MODEL = """
            module p
            data Month = { pay: Int, days: Int }
            data Ok
            data No
            behavior f : (a: Month, b: Month, c: Month) -> Ok | No
            let f (a, b, c) = {
                guard %s >= 300 else No
                Ok
            }
            """;

    private static final String SUM = "a.pay + b.pay + c.pay";

    /** The report, with where in the guard each comparison is written left out. */
    private static String measured(String total) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(total), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()))
                .replaceAll("\\d+:\\d+", "");
    }

    @Test
    void theTotalOfWhatAMapAnswersIsTheSumOfTheElementsNumbers() {
        String report = measured("List.sum(List.map(m -> m.pay, [a, b, c]))");
        assertFalse(report.contains("states no law"), report);
        assertEquals(measured(SUM), report);
    }

    @Test
    void theTotalOfElementsWrittenOutIsTheirSum() {
        String report = measured("List.sum([a.pay, b.pay, c.pay])");
        assertEquals(measured(SUM), report);
    }

    @Test
    void aTotalOfAnElementWrittenTwiceCountsItTwice() {
        String report = measured("List.sum([a.pay, a.pay, b.pay])");
        assertEquals(measured("a.pay + a.pay + b.pay"), report);
    }

    @Test
    void aTotalBehindAnAdditionOfTheFoldIsTheSum() {
        String report = measured("List.fold((acc, m) -> acc + m.pay, 0, [a, b, c])");
        assertEquals(measured(SUM), report);
    }

    @Test
    void aTotalThatIsDividedByAWrittenNumberIsTheSumDividedByIt() {
        String report = measured("List.sum(List.map(m -> m.pay, [a, b, c])) / 3");
        assertEquals(measured("(a.pay + b.pay + c.pay) / 3"), report);
    }

    @Test
    void aTotalOverWhatAFilterKeepsOnTheRowIsNotTheSumOfAll() {
        String report = measured(
                "List.sum(List.filter(p -> p >= 100, List.map(m -> m.pay, [a, b, c])))");
        assertNotEquals(measured(SUM), report);
    }

    @Test
    void aWalkWhoseStepScalesWhatItCarriedIsReadAsThatForm() {
        String report = measured("List.fold((acc, m) -> acc * 2 + m.pay, 0, [a, b, c])");
        assertEquals(measured("(a.pay * 2 + b.pay) * 2 + c.pay"), report);
    }

    @Test
    void aWalkWhoseStepIsNotAnAdditionIsNotTheSum() {
        String report = measured("List.fold((acc, m) -> acc * m.pay, 1, [a, b, c])");
        assertNotEquals(measured(SUM), report);
    }

    @Test
    void aTotalOfOneElementIsThatElement() {
        String report = measured("List.sum([a.pay])");
        assertTrue(report.contains("read as f/a.pay"), "a line is drawn on it: " + report);
        assertEquals(measured("a.pay"), report);
    }

    @Test
    void anElementWrittenTwiceDrawsTheLineItsDoubleDraws() {
        String report = measured("List.sum([a.pay, a.pay])");
        assertTrue(report.contains("read as f/a.pay"), "a line is drawn on it: " + report);
        assertEquals(measured("a.pay + a.pay"), report);
    }
}
