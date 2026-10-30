package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;
import souther.compiler.report.WhyAPlaceIsUndividedIsSaid;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of two whole numbers whose reading stops short of the input is a line on how far
 * apart its sides come out, and each row stands on it where its run worked them out.
 *
 * <p>The reading stopping says nothing of where the input has to be, so the line divides none of
 * the places the comparison names. What a row's run worked out at the comparison says where the
 * row is, so the border on it is measured as any border is: the rows on both sides, at the line
 * and beside it, and past it — and a point no row stands at is looked for by running candidates.
 *
 * <p>A streak at the end of a list is no count of anything, so the fold here is read by no form
 * and only its runs place a row.
 */
class AComparisonOverANumberOnlyARunWorksOutIsMeasuredOnTheRunsTest {

    private static final String THROUGH_A_CALL = """
            module m

            behavior misses : (xs: List<Int>) -> Int

            let misses (xs) = List.fold((n, x) -> if x == 0 then n + 1 else 0, 0, xs)

            behavior out : (xs: List<Int>) -> Bool

            let out (xs) = misses(xs) >= 3

            example misses
                | ([0]) -> 1
                | ([1]) -> 0
                | ([-1]) -> 0
                | ([-2]) -> 0
                | ([2]) -> 0
                | ([0, 0]) -> 2
            """;

    private static final String INLINE = """
            module m

            behavior out : (xs: List<Int>) -> Bool

            let out (xs) = List.fold((n, x) -> if x == 0 then n + 1 else 0, 0, xs) >= 3
            """;

    /** The rows the issue writes, on both sides of the line, at two and at three. */
    private static final List<String> ROWS = List.of("([]) -> false", "([0]) -> false",
            "([1]) -> false", "([-1]) -> false", "([-2]) -> false", "([2]) -> false",
            "([0, 0]) -> false", "([0, 0, 0]) -> true", "([0, 0, 1]) -> false");

    private static final String PAST_THE_LINE = "([0, 0, 0, 0]) -> true";

    /** What the report says of the places such a comparison names. */
    static final String MEASURED_ON_ITS_RUNS =
            WhyAPlaceIsUndividedIsSaid.of(UndividedPosition.Reason.RULE_MEASURED_ON_ITS_RUNS);

    private static Compilation compiled(String model, List<String> rows) {
        String source = model + "\nexample out\n" + rows.stream().map(row -> "    | " + row)
                .collect(Collectors.joining("\n")) + "\n";
        Compilation compilation = Compilation.ofSource(source, "Main");
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String report(String model, List<String> rows) {
        Compilation compilation = compiled(model, rows);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> and(List<String> rows, String row) {
        return Stream.concat(rows.stream(), Stream.of(row)).toList();
    }

    private static String adequacy(String report) {
        return report.lines().filter(line -> line.startsWith("adequacy: ")).findFirst()
                .orElse("");
    }

    /** Read through a call, the comparison is a line on the runs and is not left unread. */
    @Test
    void theComparisonIsALineOnHowFarApartItsSidesCameOut() {
        String report = report(THROUGH_A_CALL, ROWS);

        assertFalse(report.contains("not read"), report);
        assertTrue(report.contains(MEASURED_ON_ITS_RUNS), report);
        assertTrue(report.contains("misses(xs) - 3"), report);
    }

    /**
     * The rows the issue writes are at the line and beside it, and none is past it: a row at four
     * is owed, and found by running candidates, so the measure is short of a row and not of a
     * reading.
     */
    @Test
    void aRowPastTheLineIsOwedAndFound() {
        String report = report(THROUGH_A_CALL, ROWS);

        assertEquals("adequacy: not satisfied", adequacy(report), report);
        assertTrue(report.contains("no row is at an IN point"), report);
    }

    @Test
    void withARowPastTheLineEveryPointIsMet() {
        assertEquals("adequacy: satisfied",
                adequacy(report(THROUGH_A_CALL, and(ROWS, PAST_THE_LINE))));
        assertEquals("adequacy: satisfied", adequacy(report(INLINE, and(ROWS, PAST_THE_LINE))));
    }

    /** What is offered for the row past the line is a row whose run is past it. */
    @Test
    void theRowOfferedPastTheLineIsOneWhoseRunIsPastIt() {
        Compilation compilation = compiled(THROUGH_A_CALL, ROWS);
        String offered = GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("m")), Map.of(),
                SourceRendering.namedByIdentity(compilation.texts()), compilation.db()).text();

        assertTrue(offered.contains("([0, 0, 0, 0])"), offered);
    }

    /**
     * A point reached only by moving a whole number and a list together is reached: every
     * candidate is tried, and none is left out by the order they come in.
     */
    @Test
    void aPointOnlyANumberAndALengthTogetherReachIsFound() {
        String report = report("""
                module m

                behavior misses : (xs: List<Int>) -> Int

                let misses (xs) = List.fold((n, x) -> if x == 0 then n + 1 else 0, 0, xs)

                behavior out : (xs: List<Int>, n: Int) -> Bool

                let out (xs, n) = misses(xs) + n >= 7
                """, List.of("([], 0) -> false", "([0], 0) -> false"));

        assertTrue(report.contains("no row is at the ON point"), report);
        assertTrue(report.contains("no row is at an IN point"), report);
        assertFalse(report.contains("could show a row can be written"), report);
    }

    /**
     * A comparison a closure handed to {@code List.all} holds is visited once for each element it
     * gets to, and a row stands where some visit its run made came out. An element past the first
     * that fails is never visited: a run that stopped there says nothing of the elements after.
     */
    @Test
    void onlyTheVisitsARunMadePlaceARow() {
        String model = """
                module m

                behavior streak : (xs: List<Int>, p: Int) -> Int

                let streak (xs, p) = List.fold((n, x) -> if x == p then n + 1 else 0, 0, xs)

                behavior out : (xs: List<Int>, ps: List<Int>) -> Bool

                let out (xs, ps) = List.all(p -> streak(xs, p) >= 2, ps)
                """;
        String atTheLine = "read as out/streak(xs, p) - 2: = 0";

        String stoppedBefore = report(model, List.of("([0, 0], [1, 0]) -> false"));
        assertTrue(stoppedBefore.contains(atTheLine), stoppedBefore);

        String visited = report(model, List.of("([0, 0], [1, 0]) -> false",
                "([0, 0], [0, 1]) -> false"));
        assertFalse(visited.contains(atTheLine), visited);
    }

    /**
     * Where the reading stopped decides, and not what else the comparison holds: stopped at a
     * remainder of where an element stands, which no call or walk works out, the comparison is
     * said as a form this compiler does not read though a call stands beside the remainder.
     */
    @Test
    void aStopBesideACallIsSaidAsWhatItStoppedAt() {
        String report = report("""
                module m

                behavior misses : (xs: List<Int>) -> Int

                let misses (xs) = List.fold((n, x) -> if x == 0 then n + 1 else 0, 0, xs)

                behavior out : (xs: List<Int>) -> List<Bool>

                let out (xs) = List.mapIndexed((i, x) -> Int.floorMod(i, 2) + misses(xs) >= 1, xs)
                """, List.of("([0]) -> [true]"));

        assertFalse(report.contains(MEASURED_ON_ITS_RUNS), report);
        assertTrue(report.contains("not read"), report);
    }

    /** The row at three is the one at the line, and the row at two the one beside it. */
    @Test
    void theRowsAtThreeAndTwoAreTheOnesAtTheLineAndBesideIt() {
        List<String> all = and(ROWS, PAST_THE_LINE);
        String noThree = report(THROUGH_A_CALL,
                all.stream().filter(row -> !row.startsWith("([0, 0, 0])")).toList());
        String noTwo = report(THROUGH_A_CALL,
                all.stream().filter(row -> !row.startsWith("([0, 0])")).toList());

        assertTrue(noThree.contains("no row is at the ON point"), noThree);
        assertTrue(noTwo.contains("no row is at the OFF point"), noTwo);
    }
}
