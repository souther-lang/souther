package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.time.Duration;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A mean over the months a filter keeps is read once, and its ways of keeping are held as how
 * they are written out. A window of months whose ways are more than a reading is allowed to make
 * is read to the end, since reading it makes the reading, a condition for each month and a form
 * for each month, and writes the ways out only where a reader asks for them.
 */
class AMeanOverAWindowOfManyMonthsIsReadWithoutWritingOutItsWaysTest {

    /** Seven months come to 128 ways of keeping, more than a statement is written out from at
     *  once. */
    private static final int MONTHS = 7;

    private static final String MEAN =
            "List.sum(List.map(r -> r.pay, payable(w))) / List.length(payable(w)) >= 100";

    /** Both tests read the one report of the one model. */
    private static String memo;

    private static synchronized String report() {
        if (memo == null) {
            memo = report(MONTHS, MEAN);
        }
        return memo;
    }

    private static String report(int count, String mean) {
        String window = IntStream.rangeClosed(1, count).mapToObj(i -> "m" + i + ": Month")
                .collect(Collectors.joining(", "));
        String months = IntStream.rangeClosed(1, count).mapToObj(i -> "w.m" + i)
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
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()))
                .replaceAll("\\d+:\\d+", "");
    }

    @Test
    void aMeanOverManyMonthsIsReadWhereItsWaysAreMoreThanAReadingMakes() {
        String report = assertTimeoutPreemptively(Duration.ofSeconds(60), () -> report());
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
    }

    /**
     * A mean whose cases come to more parts than a step is concluded with is given up as one part
     * nothing read, said once. Said at every step of the cases that was past the figure, the
     * report grew with the ways.
     */
    @Test
    void aMeanWhoseCasesAreGivenUpIsSaidOnceAndNotAtEveryStepOfThem() {
        String report = assertTimeoutPreemptively(Duration.ofSeconds(60), () -> report());
        long said = report.lines().filter(line -> line.contains("not read: comparison")).count();
        assertTrue(said <= MONTHS, () -> "said " + said + " times, once for each month at most");    }
}
