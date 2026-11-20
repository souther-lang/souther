package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operation a run works out over a value that is no number of the input — what a walk came to,
 * what an option holds — may end the run where no row says. Where a run gets to the comparison and
 * works one out, the report does not read it as one that stops nothing: it says the stops of what
 * is worked out are not all told and the measurement is partial. That what the value may come to
 * takes the operation past its type shows no run that does, so it is never said as one a run may
 * stop in. The line the comparison draws stays where it was read. Where no run works the operation
 * out, or what the value comes to on the way keeps it within its type, it says nothing of the
 * kind.
 */
class AnOperationOverWhatAWalkCameToIsNotReadAsOneThatStopsNothingTest {

    private static final String THE_WALK = "List.fold((w, l) -> if l > w then l else w, 0, ds)";

    private static final String NOT_ALL_TOLD = "an operation that may end the run where nothing"
            + " here says";

    private static final String MAY_STOP = "may stop a run";

    private static final String STOP_NOT_RESOLVED = "stop not resolved:";

    /** What the walk comes to is the seed or an element, any {@code Int}, so nothing keeps one
     *  more within the type, and nothing shows a run that takes it past. */
    @Test
    void aSumOverWhatAFoldCameToIsNotReadAsOneThatStopsNothing() {
        String report = reportOf(THE_WALK + " + 1 <= 10");
        assertTrue(report.contains(NOT_ALL_TOLD), report);
        assertFalse(report.contains(MAY_STOP), report);
    }

    /** Every element the way leaves is below the greatest {@code Int}, and the seed is nought, so
     *  what the walk comes to keeps one more within the type. */
    @Test
    void nothingIsToldWhereATestOfEveryElementKeepsTheWalkWithinItsType() {
        String report = reportOf("List.all(x -> x < 9223372036854775807, ds) && " + THE_WALK
                + " + 1 <= 10");
        assertFalse(report.contains(NOT_ALL_TOLD), report);
    }

    /** A list the way leaves holding no element walks to its seed. */
    @Test
    void nothingIsToldWhereTheWayLeavesTheListHoldingNoElement() {
        String report = reportOf("List.length(ds) < 1 && " + THE_WALK + " + 1 <= 10");
        assertFalse(report.contains(NOT_ALL_TOLD), report);
    }

    /** The same walk over a list written out comes to its seed or one of its elements, and one
     *  more is still an {@code Int}. */
    @Test
    void nothingIsToldWhereWhatTheFoldCameToKeepsTheOperationWithinItsType() {
        String report = reportOf("List.fold((w, l) -> if l > w then l else w, 0, [1, 2]) + 1 <= 10");
        assertFalse(report.contains(MAY_STOP), report);
        assertFalse(report.contains(NOT_ALL_TOLD), report);
    }

    @Test
    void aSumOverWhatAnOptionHoldsIsNotReadAsOneThatStopsNothing() {
        String report = reportOf("Option.withDefault(0, List.max(ds)) + 1 <= 10");
        assertTrue(report.contains(NOT_ALL_TOLD), report);
        assertTrue(report.contains("measurement: partial"), report);
    }

    @Test
    void aStopThatIsToldIsToldAsItWas() {
        String report = reportOf("q + 1 <= 10");
        assertTrue(report.contains("every run stops in q + 1"), report);
        assertFalse(report.contains(NOT_ALL_TOLD), report);
        assertTrue(report.contains("measurement: complete"), report);
    }

    @Test
    void nothingIsToldWhereTheOperationAddsNothing() {
        String report = reportOf(THE_WALK + " + 0 <= 10");
        assertFalse(report.contains(NOT_ALL_TOLD), report);
    }

    @Test
    void nothingIsToldWhereAGuardKeepsTheOperationWithinItsType() {
        String report = reportOf(
                "(if q == 9223372036854775807 then 0 else q) + 1 <= 10");
        assertFalse(report.contains(NOT_ALL_TOLD), report);
    }

    /** A remainder by a number written, given to a name, lies below it, so one more is still an
     *  {@code Int}. */
    @Test
    void aRemainderByANameGivenAWrittenNumberKeepsTheOperationWithinItsType() {
        String report = reportOf("let k = 11", "Int.floorMod(" + THE_WALK + ", k) + 1 <= 10");
        assertFalse(report.contains(NOT_ALL_TOLD), report);
    }

    private static final String ANOTHER_WALK = "List.fold((w, l) -> if l > w then l else w, 1, ds)";

    /** A stop that is told is not the one left untold beside it: the rule is said to be one a
     *  run may stop in, and the sum over what the walk came to is said all the same. A run works
     *  out that sum in the same comparison as the sum over the input, so no existence of a run
     *  stopping is shown, and the stop is said as not resolved. */
    @Test
    void aStopToldBesideOneLeftUntoldIsSaidAsBoth() {
        String report = reportOf(THE_WALK + " + 1 <= q + 1");
        assertTrue(report.contains(STOP_NOT_RESOLVED), report);
        assertTrue(report.contains(NOT_ALL_TOLD), report);
    }

    @Test
    void aSumOverTwoValuesHeldAsideIsNotReadAsOneThatStopsNothing() {
        String report = reportOf(THE_WALK + " + " + ANOTHER_WALK + " + 1 <= 10");
        assertTrue(report.contains(NOT_ALL_TOLD), report);
        assertTrue(report.contains("measurement: partial"), report);
    }

    /** What adds up the addends of the comparison is answered for by what drew its line. */
    @Test
    void aSumOfTheAddendsOfTheComparisonIsTheAnswerOfWhatDrewItsLine() {
        String report = reportOf(THE_WALK + " + " + ANOTHER_WALK + " <= 10");
        assertFalse(report.contains(NOT_ALL_TOLD), report);
    }

    /** The operation is over a value that is not the first the reading stopped at. */
    @Test
    void aSumOverAnotherValueHeldAsideIsNotReadAsOneThatStopsNothing() {
        String report = reportOf(THE_WALK + " <= Option.withDefault(0, List.max(ds)) + 1");
        assertTrue(report.contains(NOT_ALL_TOLD), report);
    }

    /** A comparison whose arithmetic is not read says what it could not read, and nothing of
     *  what a run works out to evaluate it. */
    @Test
    void aComparisonWhoseArithmeticIsNotReadSaysNothingOfWhatIsWorkedOut() {
        String report = reportOf("Int.floorMod(" + THE_WALK + ", q) + 1 <= 10");
        assertFalse(report.contains(NOT_ALL_TOLD), report);
        assertTrue(report.contains("not a constant"), report);
    }

    /** What the report says of the line the comparison draws is what it says without the
     *  operation: the reason holds the border open and takes no line from it. */
    @Test
    void theReasonIsAddedToWhatTheReportSaysAndTakesNothingFromIt() {
        assertEquals(withoutTheReason(reportOf(THE_WALK + " + 0 <= 10")),
                withoutTheReason(reportOf(THE_WALK + " + 1 <= 10")));
    }

    private static List<String> withoutTheReason(String report) {
        return report.lines().filter(line -> line.contains("no line:")
                        || line.contains("divided no way")
                        || line.contains("whether a row is at")
                        || line.contains("read as "))
                .map(line -> line.replaceAll("@\\d+:\\d+", "@")).toList();
    }

    @Test
    void nothingIsToldWhereNoRunGetsToTheOperation() {
        String report = reportOf("(if q > 5 && q < 3 then " + THE_WALK + " + 1 else 3) >= q");
        assertFalse(report.contains(NOT_ALL_TOLD), report);
    }

    @Test
    void nothingIsToldWhereTheClosureIsAppliedToNothing() {
        String report = reportOf("List.all(r -> " + THE_WALK + " + 1 <= 10, [])");
        assertFalse(report.contains(NOT_ALL_TOLD), report);
    }

    private static String reportOf(String condition) {
        return reportOf("let unused = 0", condition);
    }

    private static String reportOf(String given, String condition) {
        Compilation compilation = ACompiledModel.measured("""
                module m

                behavior role : (ds: List<Int>, q: Int) -> Int
                let role (ds, q) = {
                    %s
                    if %s then 1 else 2
                }
                """.formatted(given, condition), new Adequacy.Asked(Adequacy.Level.OFF, false));
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
