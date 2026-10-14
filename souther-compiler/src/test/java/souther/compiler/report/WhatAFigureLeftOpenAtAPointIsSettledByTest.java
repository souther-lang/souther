package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point a figure of this compiler's left open is said to be settled by what the model can say,
 * and saying it settles it.
 *
 * <p>No option of this compiler sets the figures it stops at, so a reader told to run again allowing
 * more has nothing to do it with. What they can do is write a row at the point, or a rule that
 * leaves no value there.
 *
 * <p>The model here is one this compiler cannot build sets of beyond one element for: it offers a
 * date for an element and steps nothing from it. Rows up to four dates are written, and the region
 * past four is left to the search, which stops at how many values a point is tried with.
 */
class WhatAFigureLeftOpenAtAPointIsSettledByTest {

    private static final String MODEL = """
            module probe.dates

            behavior h : (s: Set<Date>) -> Int
            let h (s) = if Set.size(s) == 3 then 1 else 0

            example h
                | "none"  : ([]) -> 0
                | "one"   : ([Date("2026-01-01")]) -> 0
                | "two"   : ([Date("2026-01-01"), Date("2026-01-02")]) -> 0
                | "three" : ([Date("2026-01-01"), Date("2026-01-02"), Date("2026-01-03")]) -> 1
                | "four"  : ([Date("2026-01-01"), Date("2026-01-02"), Date("2026-01-03"),
                              Date("2026-01-04")]) -> 0
            %s""";

    private static final String FIVE = """
                | "five"  : ([Date("2026-01-01"), Date("2026-01-02"), Date("2026-01-03"),
                              Date("2026-01-04"), Date("2026-01-05")]) -> 0
            """;

    private static AdequacyReport measured(String rows) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(rows), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    private static String human(AdequacyReport report) {
        return report.human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** What keeps it open is the region past four, and what is said of it is what to write. */
    @Test
    void theRegionAFigureLeftOpenIsSaidToBeSettledByARowOrARule() {
        AdequacyReport report = measured("");

        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED, report.adequacy(),
                () -> human(report));
        assertTrue(human(report).contains("""
                  what keeps it open
                    stopped at a figure of this compiler     1
                    stopped at no figure                     0
                      the comparison = 3 (in the region, above) — the search stopped at how many \
                values a point is tried with (VALUES_A_POINT_IS_TRIED_WITH, 8), which no option \
                sets: write a row there, or a rule that leaves no value there
                """), human(report));
        assertFalse(human(report).contains("allowing more"), human(report));
    }

    /** And a row written there settles it. */
    @Test
    void aRowWrittenThereSettlesIt() {
        AdequacyReport report = measured(FIVE);

        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, report.adequacy(),
                () -> human(report));
    }
}
