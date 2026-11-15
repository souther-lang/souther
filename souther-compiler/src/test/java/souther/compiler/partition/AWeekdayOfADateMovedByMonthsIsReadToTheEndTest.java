package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.test.Nightly;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The weekday of any date moved by months, whatever day of its month the date is, is taken apart
 * into more cases than a line is taken apart into. It stops there and says so, and the cases of
 * the move are not what it is told for.
 *
 * <p>Deferred to the nightly: the weekday is measured in full over every month and leap year the
 * move is defined by, which takes about half a minute, and no cheaper question reaches the
 * figure it stops at. What a change to the reading of a move breaks here is as well found by the
 * morning as by the change. {@code ADateMovedByMonthsIsReadWhereItsDaysAreKnownTest} is what a
 * change waits on.
 */
@Nightly
class AWeekdayOfADateMovedByMonthsIsReadToTheEndTest {

    private static final String MODEL = """
            module demo

            behavior f : (x: Date, sunday: Date) -> Bool
            let f (x, sunday) = Int.floorMod(Date.daysBetween(sunday, Date.addMonths(1, x)), 7) >= 1
            """;

    @Test
    void theWeekdayOfAnyDateMovedByMonthsStopsAtTheCasesAndSaysSo() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        String report = AdequacyReport.of(ACompiledModel.compiles(compilation))
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("CASES_A_LINE_IS_TAKEN_APART_INTO"), report);
        assertFalse(report.contains("a date moved by months"), report);
    }
}
