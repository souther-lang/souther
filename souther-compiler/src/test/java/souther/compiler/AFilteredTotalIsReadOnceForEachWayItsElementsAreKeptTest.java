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
     * the two relate the pay of one pair to the pay of the other, which a total read for one of
     * them and used for both could not.
     */
    @Test
    void theSameHelperHandedOtherValuesIsAnotherTotal() {
        String report = report("""
                let total (a: Month, b: Month): Int =
                    List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ a, b ])))
                """ + guarded("total(p.x, p.y) >= total(p.u, p.v) + 100"));
        assertTrue(report.contains("read as f/p.u.pay: = p.x.pay - 100"), report);
        assertTrue(report.contains("read as f/p.u.pay: = p.y.pay - 100"), report);
        assertTrue(report.contains("read as f/p.u.pay + p.v.pay: = -100"), report);
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
     * A filter is handed only what the one inside it kept, so a chain of them is as many ways as
     * it has filters and one more. Read as every combination of their truths, the ways of this
     * chain would be more than one condition is read in.
     */
    @Test
    void aChainOfFiltersIsAsManyWaysAsItHasFiltersAndOneMore() {
        StringBuilder list = new StringBuilder("[ p.x ]");
        for (int days = 1; days <= 10; days++) {
            list = new StringBuilder("List.filter(r -> r.days >= " + days + ", " + list + ")");
        }
        String report = report(guarded("List.sum(List.map(r -> r.pay, " + list + ")) >= 900"));
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
        assertTrue(report.contains("read as f/p.x.pay"), report);
    }

    /**
     * The way that keeps the element no form can be made of stops, and says what the element is;
     * what keeps it is still read, as a condition of its own.
     */
    @Test
    void aWayThatKeepsAnElementWithNoFormSaysWhatTheElementIs() {
        String report = report(guarded("""
                List.sum(List.map(r -> r.pay * r.days, List.filter(r -> r.days >= 17, [ p.x ])))
                    >= p.y.pay"""));
        assertTrue(report.contains("compares a product of two values that are not constants"),
                report);
        assertFalse(report.contains("states no law"), report);
        assertTrue(report.contains("read as f/p.x.days: = 17"), report);
    }
}
