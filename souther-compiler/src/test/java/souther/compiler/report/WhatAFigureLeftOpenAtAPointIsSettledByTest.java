package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

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
 * <p>The model here is one this compiler cannot build sets of beyond one element for: between two
 * decimals there is no next one, so it offers one decimal for an element and steps nothing from it.
 * Rows up to four decimals are written, and the region past four is left to the search, which stops
 * at how many values a point is tried with.
 */
class WhatAFigureLeftOpenAtAPointIsSettledByTest {

    private static final String MODEL = """
            module probe.sizes

            behavior h : (s: Set<Decimal>) -> Int
            let h (s) = if Set.size(s) == 3 then 1 else 0

            example h
                | "none"  : ([]) -> 0
            %s%s%s%s%s""";

    /** A row of a set of {@code size} decimals, from nought up. */
    private static String row(String name, int size, int answer) {
        return "    | \"%s\" : ([%s]) -> %d\n".formatted(name, IntStream.range(0, size)
                .mapToObj(i -> i + ".5m").collect(Collectors.joining(", ")), answer);
    }

    private static AdequacyReport measured(String rows) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(
                row("one", 1, 0), row("two", 2, 0), row("three", 3, 1), row("four", 4, 0), rows),
                "Main");
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
                      the comparison (in the region, above) — the search stopped at how many \
                values a point is tried with (VALUES_A_POINT_IS_TRIED_WITH, 8), which no option \
                sets: a row there, or a rule that leaves no value there, would settle it; \
                nothing shows one is needed
                """), human(report));
        assertFalse(human(report).contains("allowing more"), human(report));
    }

    /** And a row written there settles it. */
    @Test
    void aRowWrittenThereSettlesIt() {
        AdequacyReport report = measured(row("five", 5, 0));

        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, report.adequacy(),
                () -> human(report));
    }
}
