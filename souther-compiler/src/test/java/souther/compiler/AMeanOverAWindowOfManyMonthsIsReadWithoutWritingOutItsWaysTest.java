package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.time.Duration;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A mean over the months a filter keeps is read once, and its ways of keeping are held as how
 * they are written out. A window of months whose ways are more than a reading is allowed to make
 * is read to the end, since reading it makes the reading, a condition for each month and a form
 * for each month, and writes the ways out only where a reader asks for them.
 */
class AMeanOverAWindowOfManyMonthsIsReadWithoutWritingOutItsWaysTest {

    private static final int MONTHS = 10;

    private static String report(String mean) {
        String window = IntStream.rangeClosed(1, MONTHS).mapToObj(i -> "m" + i + ": Month")
                .collect(Collectors.joining(", "));
        String months = IntStream.rangeClosed(1, MONTHS).mapToObj(i -> "w.m" + i)
                .collect(Collectors.joining(", ", "[ ", " ]"));
        Compilation compilation = Compilation.ofSource("""
                module p
                data Month = { pay: Int, days: Int }
                data Win = { %s }
                data Ok
                data No
                let payable (w: Win): List<Month> =
                    List.filter(r -> r.days >= 17, %s)
                behavior f : (w: Win) -> Ok | No
                let f (w) = {
                    guard %s else No
                    Ok
                }
                """.formatted(window, months, mean), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()))
                .replaceAll("\\d+:\\d+", "");
    }

    @Test
    void aMeanOverManyMonthsIsReadWhereItsWaysAreMoreThanAReadingMakes() {
        String report = assertTimeoutPreemptively(Duration.ofSeconds(60), () -> report(
                "List.sum(List.map(r -> r.pay, payable(w))) / List.length(payable(w)) >= 100"));
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
    }
}
