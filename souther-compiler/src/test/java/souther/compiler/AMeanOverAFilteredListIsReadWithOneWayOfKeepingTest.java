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

    /**
     * The mean was read, and nothing of it was left unread.
     *
     * <p>Not that the measurement is complete. The total of the kept elements is one decision per
     * element meeting at the sum, and these models start with a guard on how many are kept, which
     * names no position a row can be steered by. A row cannot be steered to the meeting, so the
     * measure says it is partial for that and for nothing in how the mean is read.
     */
    private static void assertReadToTheEnd(String report) {
        assertFalse(report.contains(NO_QUOTIENT_READ), report);
        assertFalse(report.contains("not read"), report);
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
        assertReadToTheEnd(report);
    }

    /** The same mean against what it is: it is held wherever an element is kept, so the way that
     *  fails it is the one no input takes. */
    @Test
    void aMeanEveryRunHasIsReadAsHeld() {
        String report = report(guarded("List.length(" + PAYABLE + ") >= 1",
                meanOfEach("100") + " >= 100"));
        assertEquals("· the comparison at  does not hold", whatLeavesNoValue(report), report);
        assertReadToTheEnd(report);
    }

    /**
     * Where no element is kept the count is nought and the division stops: it is no mean of
     * nought. Were it read as one, a mean of 100 against 100 would fail on those rows and the way
     * that fails it would be taken; against 101 it would fail the same way and the way that holds
     * it would be taken by none. Each is taken by no input, whichever the mean is held against.
     */
    @Test
    void aMeanOverNothingKeptIsTheDivisionByZeroTheLanguageStopsAt() {
        String held = report(guarded(meanOfEach("100") + " >= 100"));
        assertEquals("· the comparison at  does not hold", whatLeavesNoValue(held), held);
        String failed = report(guarded(meanOfEach("100") + " >= 101"));
        assertEquals("· the comparison at  holds", whatLeavesNoValue(failed), failed);
    }

    private static String overAHelpersListOfThree(String element, String held) {
        return report("""
                data Win = { first: Month, second: Month, third: Month }
                let payable (w: Win): List<Month> =
                    List.filter(r -> r.days >= 17, [ w.first, w.second, w.third ])
                behavior g : (w: Win) -> Ok | No
                let g (w) = {
                    guard List.length(payable(w)) >= 1 else No
                    guard List.sum(List.map(r -> %s, payable(w)))
                            / List.length(payable(w)) >= %s else No
                    Ok
                }
                """.formatted(element, held));
    }

    /**
     * The mean as the shape the helper gives it, over three elements, with every kept element
     * worth 100: read to the end, and as the mean of 100 it is.
     */
    @Test
    void aMeanOverAHelpersListOfThreeIsReadAsWhatItIs() {
        String failed = overAHelpersListOfThree("100", "101");
        assertEquals("· the comparison at  holds", whatLeavesNoValue(failed), failed);
        assertReadToTheEnd(failed);
        String held = overAHelpersListOfThree("100", "100");
        assertEquals("· the comparison at  does not hold", whatLeavesNoValue(held), held);
        assertReadToTheEnd(held);
    }

    /**
     * With the pay of each month the comparison is a line over several of the inputs, which the
     * reading does not divide the input by, as it does not for the same comparison written out
     * without a filter. What it stops at is that, and no longer the quotient.
     */
    @Test
    void aMeanOverTheirPayStopsAtTheLineOverSeveralValuesAndNotAtTheQuotient() {
        String report = overAHelpersListOfThree("r.pay", "300");
        assertFalse(report.contains(NO_QUOTIENT_READ), report);
        assertTrue(report.contains("several lines held together"), report);
    }
}
