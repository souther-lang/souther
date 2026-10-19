package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

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
    void aRangeOfWrittenBoundsIsTheListOfItsNumbers() {
        String report = measured("List.sum(List.map(n -> a.pay + n, List.rangeInclusive(1, 3)))");
        assertFalse(report.contains("states no law"), report);
        assertEquals(measured("List.sum(List.map(n -> a.pay + n, [1, 2, 3]))"), report);
    }

    @Test
    void aRangeWhoseStartIsPastItsEndHoldsNothing() {
        String report = measured("a.pay + List.sum(List.rangeInclusive(3, 1))");
        assertEquals(measured("a.pay"), report);
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
    void aTotalOverWhatAFilterKeepsOnTheRowIsTheSumOfWhatEachWayOfKeepingKeeps() {
        String report = measured(
                "List.sum(List.map(m -> m.pay, List.filter(m -> m.days >= 17, [a, b])))");
        assertEquals(linesOnPay(measured("(if a.days >= 17 then a.pay else 0)"
                + " + (if b.days >= 17 then b.pay else 0)")), linesOnPay(report));
        assertNotEquals(linesOnPay(measured("a.pay + b.pay")), linesOnPay(report));
    }

    /** The lines the report draws on a number of pay, each once. */
    private static Set<String> linesOnPay(String report) {
        return report.lines().filter(line -> line.contains("read as") && line.contains("pay"))
                .map(String::strip).collect(Collectors.toSet());
    }

    @Test
    void anElementThatIsNoFormStopsOnlyTheWaysThatKeepIt() {
        String report = measured("List.sum(List.map(m -> m.pay * m.days,"
                + " List.filter(m -> m.days >= 17, [a, b])))");
        assertTrue(report.contains("not read"), report);
        assertFalse(report.contains("states no law"), report);
    }

    @Test
    void aWalkWhoseStepScalesWhatItCarriedIsReadAsThatForm() {
        String report = measured("List.fold((acc, m) -> acc * 2 + m.pay, 0, [a, b, c])");
        assertEquals(measured("(a.pay * 2 + b.pay) * 2 + c.pay"), report);
    }

    /**
     * The elements of a walk from the end arrive last to first, so unrolled in the order they are
     * written the step would be read on other numbers: {@code 4 * a.pay + 4} and not
     * {@code a.pay + 10}.
     */
    @Test
    void aWalkFromTheEndIsNotUnrolledInTheOrderTheListIsWritten() {
        String report = measured("List.foldRight((m, acc) -> acc * 2 + m, 0, [a.pay, 1, 2])");
        assertTrue(report.contains("not read"), report);
        assertFalse(report.contains("= 74"), "the line of 4 * a.pay + 4: " + report);
        assertTrue(measured("a.pay + 10").contains("read as f/a.pay: = 290"),
                "the line the walk would draw were it read");
    }

    @Test
    void aWalkOverAContainerWithNoOrderIsNotUnrolled() {
        String report = measured("Set.fold((acc, m) -> acc * 2 + m, 0, Set.fromList([a.pay, 1]))");
        assertTrue(report.contains("not read"), report);
    }

    @Test
    void aWalkWhoseStepIsNotAnAdditionIsNotTheSum() {
        String report = measured("List.fold((acc, m) -> acc * m.pay, 1, [a, b, c])");
        assertTrue(report.contains("not read"), report);
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
