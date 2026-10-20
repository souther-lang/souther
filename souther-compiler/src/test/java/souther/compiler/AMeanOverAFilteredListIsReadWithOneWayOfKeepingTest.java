package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The total and the count of a list whose elements a filter keeps are given in the same ways of
 * keeping, so a mean over it is read as the pair they are: a way that keeps a set of elements has
 * that many of them and their sum, and no way is read that no run takes.
 */
class AMeanOverAFilteredListIsReadWithOneWayOfKeepingTest {

    private static final String PREAMBLE = """
            module p
            data Month = { pay: Int, days: Int }
            data Pair = { x: Month, y: Month }
            data Ok
            data No
            """;

    private static final String PAYABLE = "List.filter(r -> r.days >= 17, [ p.x, p.y ])";

    private static final String NO_QUOTIENT_READ = "compares a quotient by a value that is not a constant";

    private static final String NO_INPUT_CONTINUES =
            "the declarations and the conditions on the way leave no value";

    private static String report(String body) {
        Compilation compilation = Compilation.ofSource(PREAMBLE + body, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()))
                .replaceAll("\\d+:\\d+", "");
    }

    private static String guarded(String... conditions) {
        StringBuilder guards = new StringBuilder();
        for (String condition : conditions) {
            guards.append("    guard ").append(condition).append(" else No\n");
        }
        return """
                behavior f : (p: Pair) -> Ok | No
                let f (p) = {
                %s    Ok
                }
                """.formatted(guards);
    }

    private static String meanOfEach(String element) {
        return "List.sum(List.map(r -> " + element + ", " + PAYABLE + ")) / List.length("
                + PAYABLE + ")";
    }

    /** The line the report gives as what no input gets past, which is the way that is never taken. */
    private static String whatLeavesNoValue(String report) {
        List<String> lines = report.lines().map(String::strip).toList();
        int at = IntStream.range(0, lines.size())
                .filter(i -> lines.get(i).endsWith(NO_INPUT_CONTINUES + ":")).findFirst()
                .orElseThrow(() -> new AssertionError(report));
        return lines.get(at + 1);
    }

    @Test
    void theCountOfAFilteredListIsReadForEachWayOfKeeping() {
        String report = report(guarded("List.length(" + PAYABLE + ") >= 2"));
        assertFalse(report.contains("not read"), report);
    }

    @Test
    void aMeanOverAFilteredListIsNoLongerStoppedAtTheQuotient() {
        String report = report(guarded("List.length(" + PAYABLE + ") >= 1",
                meanOfEach("r.pay") + " >= 300"));
        assertFalse(report.contains(NO_QUOTIENT_READ), report);
    }

    /**
     * Every kept element is worth 100, so the mean is 100 wherever one is kept. Read with the
     * total and the count apart, a way that keeps two has a total of 200 and a way that keeps one
     * a count of one, and a pair of them would make a mean of 200 or more that no run has.
     */
    @Test
    void noMeanIsReadThatNoRunHas() {
        String report = report(guarded("List.length(" + PAYABLE + ") >= 1",
                meanOfEach("100") + " >= 101"));
        assertEquals("· the comparison at  holds", whatLeavesNoValue(report), report);
        assertTrue(report.contains("measurement: complete"), report);
    }

    /** The same mean against what it is: it is held wherever an element is kept, so the way that
     *  fails it is the one no input takes. */
    @Test
    void aMeanEveryRunHasIsReadAsHeld() {
        String report = report(guarded("List.length(" + PAYABLE + ") >= 1",
                meanOfEach("100") + " >= 100"));
        assertEquals("· the comparison at  does not hold", whatLeavesNoValue(report), report);
        assertTrue(report.contains("measurement: complete"), report);
    }

    /**
     * Where no element is kept the count is nought and the division stops, so the mean is read
     * where it is guarded and is stopped on by the language where it is not.
     */
    @Test
    void aMeanOverNothingKeptIsTheDivisionByZeroTheLanguageStopsAt() {
        String report = report(guarded(meanOfEach("100") + " >= 100"));
        assertFalse(report.contains(NO_QUOTIENT_READ), report);
        assertTrue(report.contains("measurement: complete"), report);
    }
}
