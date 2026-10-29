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

    /** The same, with a pay no sum written out can carry past the greatest {@code Int}: a row that
     *  stops in {@code a.pay + a.pay} is no row at the comparison, and the total over the list is
     *  not read as one that stops. */
    private static final String SMALL_PAYS = MODEL.replace(
            "data Month = { pay: Int, days: Int }",
            "data Month = { pay: Int, days: Int }\n"
                    + "    invariant pay >= -1000000 && pay <= 1000000");

    private static final String SUM = "a.pay + b.pay + c.pay";

    /**
     * {@code report} without where every run is shown to stop. A sum written out tells each
     * addition it works out, and is shown to stop where two of the pays together pass the type; a
     * total over a list written out is one operation, and is shown to stop where the whole total
     * passes it, as is a total over what a closure makes of each element of one, once each
     * application is worked out. What else is read of them is the same.
     */
    private static String besideWhereEveryRunStops(String report) {
        return report.replaceAll("(?m)^.*may stop a run:.*every run stops.*\\R", "");
    }

    /** The report, with where in the guard each comparison is written left out. */
    private static String measured(String total) {
        return measured(MODEL, total);
    }

    private static String measured(String model, String total) {
        Compilation compilation = Compilation.ofSource(model.formatted(total), "Main");
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
        assertEquals(measured("List.sum([a.pay, b.pay, c.pay])"), report);
    }

    @Test
    void theTotalOfElementsWrittenOutIsTheirSum() {
        String report = measured("List.sum([a.pay, b.pay, c.pay])");
        assertEquals(besideWhereEveryRunStops(measured(SUM)), besideWhereEveryRunStops(report));
    }

    /**
     * The library adds the elements up exactly and holds only the total to the type, so the total
     * of {@code [max, 1, -1]} is {@code max}: a total over a list written out stops where the whole
     * total passes the type and not where the first two of its elements added written out do.
     */
    @Test
    void theTotalOfElementsWrittenOutStopsWhereTheWholeTotalPassesTheType() {
        String report = measured("List.sum([a.pay, b.pay, c.pay])");
        assertTrue(report.contains("every run stops in a.pay + b.pay + c.pay where a.pay + b.pay"
                + " + c.pay is at least 9223372036854775808"), report);
        assertFalse(report.contains("in a.pay + b.pay where"), report);
        assertTrue(measured(SUM).contains("in a.pay + b.pay where"), measured(SUM));
    }

    /** Two elements are one addition, which the total is as well. */
    @Test
    void theTotalOfTwoElementsWrittenOutStopsWhereTheirSumDoes() {
        assertEquals(measured("a.pay + b.pay"), measured("List.sum([a.pay, b.pay])"));
    }

    /** The sum written out is shown to stop where its first addition passes the type, which is
     *  what the comparisons above leave out of it. */
    @Test
    void theSumWrittenOutIsShownToStopWhereItsFirstAdditionPassesTheType() {
        assertTrue(measured(SUM).contains("every run stops in a.pay + b.pay where a.pay + b.pay"
                + " is at least 9223372036854775808"), measured(SUM));
    }

    @Test
    void aRangeOfWrittenBoundsIsTheListOfItsNumbers() {
        String report = measured("List.sum(List.map(n -> a.pay + n, List.rangeInclusive(1, 3)))");
        assertFalse(report.contains("states no law"), report);
        assertEquals(measured("List.sum(List.map(n -> a.pay + n, [1, 2, 3]))"), report);
    }

    /** A closure that never reads the element it is handed leaves that element a place no form
     *  names, which is no reason for a measure to stop with an error. */
    @Test
    void aClosureThatIgnoresItsElementIsATotalOfWhatItAnswersEachTime() {
        assertEquals(measured("a.pay + a.pay"),
                measured("List.sum(List.map(n -> a.pay, [1, 2]))"));
    }

    /** The span is never subtracted: a range ending at the largest whole number is written out. */
    @Test
    void aRangeAtTheEdgeOfTheWholeNumbersIsWrittenOutWithoutOverflowing() {
        String report = measured("List.sum(List.map(n -> a.pay,"
                + " List.rangeInclusive(9223372036854775806, 9223372036854775807)))");
        assertEquals(measured("a.pay + a.pay"), report);
    }

    @Test
    void aRangeOfMoreThanAreWrittenOutIsNotReadAndEndsAtTheFigure() {
        String report = measured("List.sum(List.map(n -> a.pay, List.rangeInclusive(1, 1025)))");
        assertTrue(report.contains("not read"), report);
        assertNotEquals(measured("a.pay"), report);
    }

    @Test
    void aRangeWhoseStartIsPastItsEndHoldsNothing() {
        String report = measured("a.pay + List.sum(List.rangeInclusive(3, 1))");
        assertEquals(measured("a.pay"), report);
    }

    @Test
    void aTotalOfAnElementWrittenTwiceCountsItTwice() {
        String report = measured(SMALL_PAYS, "List.sum([a.pay, a.pay, b.pay])");
        assertEquals(measured(SMALL_PAYS, "a.pay + a.pay + b.pay"), report);
    }

    /**
     * A fold over a list written out adds the elements one step at a time, so it works out the
     * same additions the sum written out does, in the same order, and stops where they stop.
     */
    @Test
    void aTotalBehindAnAdditionOfTheFoldIsTheSum() {
        String report = measured("List.fold((acc, m) -> acc + m.pay, 0, [a, b, c])");
        assertEquals(measured(SUM), report);
    }

    @Test
    void aTotalThatIsDividedByAWrittenNumberIsTheSumDividedByIt() {
        String report = measured("List.sum(List.map(m -> m.pay, [a, b, c])) / 3");
        assertEquals(measured("List.sum([a.pay, b.pay, c.pay]) / 3"), report);
        assertEquals(besideWhereEveryRunStops(measured("(a.pay + b.pay + c.pay) / 3")),
                besideWhereEveryRunStops(report));
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

    /**
     * The walk draws the lines of the form it is the walk of. It tells of no operation the walk
     * works out, so the comparison is not read to the end where the form written out is: what is
     * held is the lines, and not that nothing is left unread.
     */
    @Test
    void aWalkWhoseStepScalesWhatItCarriedIsReadAsThatForm() {
        String report = measured("List.fold((acc, m) -> acc * 2 + m.pay, 0, [a, b, c])");
        String written = measured("(a.pay * 2 + b.pay) * 2 + c.pay");
        assertEquals(readAs(written), readAs(report));
    }

    /** The lines of a report that say which form a border is drawn on. */
    private static Set<String> readAs(String report) {
        return report.lines().filter(line -> line.contains("read as")).map(String::strip)
                .collect(Collectors.toSet());
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
