package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.HashSet;
import java.util.List;
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
                      comparison@0:null in h (in the region, above) — the search stopped at how many \
                values a point is tried with (VALUES_A_POINT_IS_TRIED_WITH, 8), which no option \
                sets: a row there, or a rule that leaves no value there, would settle it; \
                nothing shows one is needed
                """), human(report));
        assertFalse(human(report).contains("allowing more"), human(report));
    }

    /**
     * Two behaviors each holding the verdict open at a comparison of their own: the line says which
     * comparison, so a reader is not left with "the comparison" for either.
     */
    @Test
    void aPointOfABodyComparisonIsNamedByItsPlaceAndNotByItsKind() {
        Compilation compilation = Compilation.ofSource("""
                module probe.sizes

                behavior h : (s: Set<Decimal>) -> Int
                let h (s) = if Set.size(s) == 3 then 1 else 0

                behavior g : (s: Set<Decimal>) -> Int
                let g (s) = if Set.size(s) == 2 then 1 else 0

                example h
                    | "none"  : ([]) -> 0
                %s%s%s%s
                example g
                    | "none"  : ([]) -> 0
                %s%s%s
                """.formatted(row("one", 1, 0), row("two", 2, 0), row("three", 3, 1),
                row("four", 4, 0), row("one", 1, 0), row("two", 2, 1), row("three", 3, 0)),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String human = human(AdequacyReport.of(compilation));

        List<String> points = pointsOfComparisons(human);
        assertEquals(2, points.size(), human);
        assertEquals(1, points.stream().filter(each -> each.contains(" in h ")).count(), human);
        assertEquals(1, points.stream().filter(each -> each.contains(" in g ")).count(), human);
        assertEquals(2, new HashSet<>(points).size(), human);
    }

    /** Two behaviors calling one helper, each with the rows that leave its region open. */
    private static final String ONE_HELPER_TWO_READERS = """
            module probe.sizes

            let big (s: Set<Decimal>) = Set.size(s) == 3

            behavior a : (s: Set<Decimal>) -> Int
            let a (s) = if big(s) then 1 else 0

            behavior b : (s: Set<Decimal>) -> Int
            let b (s) = if big(s) then 1 else 0

            example a
                | "none"  : ([]) -> 0
            %1$s
            example b
                | "none"  : ([]) -> 0
            %1$s
            """;

    private static Compilation measuredHelperTwoBehaviorsRead() {
        Compilation compilation = Compilation.ofSource(ONE_HELPER_TWO_READERS.formatted(
                row("one", 1, 0) + row("two", 2, 0) + row("three", 3, 1) + row("four", 4, 0)),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * A comparison written in a helper is read by each behavior that calls it, and each reading is
     * a debt of its own, so the two are two lines that differ in the behavior and in nothing else.
     * The place the comparison is written is the same for both.
     */
    @Test
    void aComparisonOfAHelperTwoBehaviorsReadIsALinePerReader() {
        Compilation compilation = measuredHelperTwoBehaviorsRead();
        String human = human(AdequacyReport.of(compilation));

        List<String> points = pointsOfComparisons(human);
        assertEquals(2, points.size(), human);
        assertEquals(1, points.stream().filter(each -> each.contains(" in a ")).count(), human);
        assertEquals(1, points.stream().filter(each -> each.contains(" in b ")).count(), human);
        assertEquals(2, new HashSet<>(points).size(), human);
    }

    /**
     * And the place it names is the one in the source the compilation was given, which the handle
     * is built from and a layout-less rendering cannot show.
     */
    @Test
    void theComparisonIsNamedByThePlaceItIsWrittenAt() {
        Compilation compilation = measuredHelperTwoBehaviorsRead();
        String human = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        List<String> points = pointsOfComparisons(human);
        assertEquals(2, points.size(), human);
        // Source, line, column: the helper is the third line of the module text, and both readers
        // are told that line and not the line of the call that reached it.
        for (String each : points) {
            assertTrue(each.contains("comparison@0:3:"), each);
        }
    }

    /**
     * The lines under {@code what keeps it open} that name a point of a comparison in a body,
     * which are the entries of that section and nothing the report says elsewhere.
     */
    private static List<String> pointsOfComparisons(String human) {
        assertTrue(human.contains("what keeps it open"), human);
        List<String> section = human.substring(human.indexOf("what keeps it open")).lines()
                .skip(1)
                .takeWhile(each -> each.startsWith("    "))
                .toList();
        assertFalse(section.stream().anyMatch(each -> each.contains("the comparison")), human);
        return section.stream().filter(each -> each.startsWith("      ")).toList();
    }

    /** And a row written there settles it. */
    @Test
    void aRowWrittenThereSettlesIt() {
        AdequacyReport report = measured(row("five", 5, 0));

        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, report.adequacy(),
                () -> human(report));
    }
}
