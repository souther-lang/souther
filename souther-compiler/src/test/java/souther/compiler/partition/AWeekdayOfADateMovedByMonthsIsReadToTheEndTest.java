package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.test.Nightly;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The weekday of any date moved by months, whatever day of its month the date is, is read in the
 * cases the move is defined by, and a row that could not be composed for a point of it says the
 * figure of this compiler that stopped the search.
 *
 * <p>What is pinned is that nothing stops silently, and not which figure does: a line taken apart
 * from each class of remainders no comparison tells apart ends where the walk branches, so the
 * cases of the move are read to the end and the search for a row is what a figure stops. A reason
 * stays where a row is not composed, and "a date moved by months" is no reason of it.
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
    void theWeekdayOfAnyDateMovedByMonthsIsReadAndEveryRowNotComposedSaysWhy() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        String report = AdequacyReport.of(ACompiledModel.compiles(compilation))
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("a date moved by months"), report);
        List<String> unbuilt = report.lines()
                .filter(line -> line.contains("nothing could show a row can be written")).toList();
        assertFalse(unbuilt.isEmpty(), report);
        unbuilt.forEach(line -> assertTrue(line.contains("a figure of this compiler's is why"),
                line));
    }
}
