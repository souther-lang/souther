package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.time.Duration;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total over a list whose elements a filter keeps is read once for each way they are kept, and
 * the ways are the ones a run can take: a filter is handed only the elements the filters inside it
 * kept, a total is its own to each place it stands, and a way that keeps an element no form can be
 * made of stops without stopping the ways that drop it.
 */
class AFilteredTotalIsReadOnceForEachWayItsElementsAreKeptTest {

    private static final String PREAMBLE = """
            module p
            data Month = { pay: Int, days: Int }
            data Pair = { x: Month, y: Month, u: Month, v: Month }
            data Ok
            data No
            """;

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

    private static String guarded(String condition) {
        return """
                behavior f : (p: Pair) -> Ok | No
                let f (p) = {
                    guard %s else No
                    Ok
                }
                """.formatted(condition);
    }

    /** The lines the report draws on a number of pay, each once. */
    private static Set<String> linesOnPay(String report) {
        return report.lines().filter(line -> line.contains("read as") && line.contains("pay"))
                .map(String::strip).collect(Collectors.toSet());
    }

    /**
     * The same helper handed other values is another total: the lines drawn on the comparison of
     * the two relate the pay of one month to the pay of the other, which a total read for one of
     * them and used for both could not. A list of one is enough to keep or not.
     */
    @Test
    void theSameHelperHandedOtherValuesIsAnotherTotal() {
        String report = report("""
                let total (a: Month): Int =
                    List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ a ])))
                """ + guarded("total(p.x) >= total(p.u) + 100"));
        assertTrue(report.contains("read as f/p.u.pay: = p.x.pay - 100"), report);
        assertTrue(report.contains("read as f/p.u.pay: = -100"), report);
    }

    @Test
    void anElementKeptByTwoFiltersDrawsTheLinesOfBothHoldingAndNoOther() {
        String filtered = report(guarded("""
                List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17,
                    List.filter(r -> r.pay >= 100, [ p.x, p.y ])))) >= 900"""));
        String written = report(guarded("""
                (if p.x.pay >= 100 then (if p.x.days >= 17 then p.x.pay else 0) else 0)
                + (if p.y.pay >= 100 then (if p.y.days >= 17 then p.y.pay else 0) else 0) >= 900"""));
        assertEquals(linesOnPay(written), linesOnPay(filtered));
    }

    /**
     * The fewest truths whose every combination is more readings than one condition is read in.
     */
    private static final int PAST_THE_READINGS = Integer.numberOfTrailingZeros(
            Integer.highestOneBit(CompositionBudget.READINGS_OF_ONE_CONDITION.maximum())) + 1;

    /**
     * A filter is handed only what the one inside it kept, so a chain of them is as many ways as
     * it has filters and one more. Read as every combination of their truths, the ways of this
     * chain would be more than one condition is read in — which the fewest filters past that
     * figure already are.
     */
    @Test
    void aChainOfFiltersIsAsManyWaysAsItHasFiltersAndOneMore() {
        StringBuilder list = new StringBuilder("[ p.x ]");
        for (int days = 1; days <= PAST_THE_READINGS; days++) {
            list = new StringBuilder("List.filter(r -> r.days >= " + days + ", " + list + ")");
        }
        String report = report(guarded("List.sum(List.map(r -> r.pay, " + list + ")) >= 900"));
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
        assertTrue(report.contains("read as f/p.x.pay"), report);
    }

    /**
     * Independent truths are as many ways as there are combinations of them, and the budget says
     * so before they are counted out. As few of them as make more combinations than the figure:
     * counted out, those are read and the total of the first is drawn, which is what says the
     * budget stopped them.
     */
    @Test
    void manyIndependentTruthsAreStoppedByTheBudgetBeforeTheyAreCountedOut() {
        int elements = PAST_THE_READINGS;
        StringBuilder fields = new StringBuilder();
        StringBuilder list = new StringBuilder();
        for (int i = 1; i <= elements; i++) {
            fields.append(i > 1 ? ", " : "").append("m").append(i).append(": Month");
            list.append(i > 1 ? ", " : "").append("w.m").append(i);
        }
        String body = "data Win = { " + fields + " }\n"
                + "behavior g : (w: Win) -> Ok | No\n"
                + "let g (w) = {\n"
                + "    guard List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ "
                + list + " ]))) >= 900 else No\n"
                + "    Ok\n}\n";
        String report = assertTimeoutPreemptively(Duration.ofSeconds(30), () -> report(body));
        assertFalse(report.contains("read as g/w.m1.pay"), report);
    }

    /**
     * The elements a way reads are charged as the elements of a total that nothing keeps are: a
     * list too long to read element by element is too long whether or not a filter is over it.
     * One element past how many times one condition is read is that, each element being a reading.
     */
    @Test
    void aListTooLongToBeReadElementByElementIsTooLongKeptOrNot() {
        String list = IntStream.range(0,
                        CompositionBudget.READINGS_OF_ONE_CONDITION.maximum() + 1)
                .mapToObj(i -> "p.x")
                .collect(Collectors.joining(", ", "[ ", " ]"));
        String plain = report(guarded("List.sum(List.map(r -> r.pay, " + list + ")) >= 900"));
        String filtered = report(guarded("List.sum(List.map(r -> r.pay, List.filter("
                + "r -> r.days >= 17, " + list + "))) >= 900"));
        assertFalse(plain.contains("read as f/p.x.pay"), plain);
        assertFalse(filtered.contains("read as f/p.x.pay"), filtered);
    }

    /**
     * The way that keeps the element no form can be made of stops, and says what the element is;
     * what keeps it is still read, as a condition of its own.
     */
    @Test
    void aWayThatKeepsAnElementWithNoFormSaysWhatTheElementIs() {
        String report = report(guarded("""
                List.sum(List.map(r -> r.pay * r.days * r.pay, List.filter(r -> r.days >= 17, [ p.x ])))
                    >= p.y.pay"""));
        assertTrue(report.contains("compares a product of two values that are not constants"),
                report);
        assertFalse(report.contains("states no law"), report);
        assertTrue(report.contains("read as f/p.x.days: = 17"), report);
    }
}
