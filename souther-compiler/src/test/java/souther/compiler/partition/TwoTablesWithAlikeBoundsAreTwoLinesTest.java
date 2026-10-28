package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison a helper holds is cut at the same places whatever table it is handed, and the bound
 * of each table is written once on its own, so a row through one table says nothing of the other.
 */
class TwoTablesWithAlikeBoundsAreTwoLinesTest {

    private static final String ALIKE = "[ Row { grade = 1, lowerBound = 0 },"
            + " Row { grade = 2, lowerBound = 100 } ]";

    private static String model(String secondTable, String call) {
        return """
                module demo

                data N = { v: Int }
                    invariant v >= 0
                data Row = { grade: Int, lowerBound: Int }
                let first: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                         Row { grade = 2, lowerBound = 100 } ]
                let second: List<Row> = %s
                let gradeIn (rows: List<Row>, m: Int): Int =
                    List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 0, rows)

                behavior f : (a: N, useFirst: Bool) -> Int

                let f (a, useFirst) =
                    %s

                """.formatted(secondTable, call);
    }

    private static final String TWO_TABLES =
            "if useFirst then gradeIn(first, a.v) else gradeIn(second, a.v)";

    /** The points at the bound and beside it, through one table and one value of the switch. */
    private static String rowsThrough(boolean useFirst) {
        return """
                    | (N { v = 100 }, %1$s) -> 2
                    | (N { v = 99 }, %1$s) -> 1
                    | (N { v = 101 }, %1$s) -> 2
                    | (N { v = 98 }, %1$s) -> 1
                """.formatted(useFirst);
    }

    private static final String HEAD = "example f\n";

    private static List<String> owedAtTheComparison(String report) {
        return report.lines().filter(each -> each.contains("no row is at"))
                .filter(each -> each.contains("(comparison@")).toList();
    }

    @Test
    void rowsThroughTheFirstTableLeaveTheSecondOwed() {
        String report = reportOf(model(ALIKE, TWO_TABLES) + HEAD + rowsThrough(true));
        List<String> owed = owedAtTheComparison(report);
        assertTrue(owed.stream().anyMatch(each -> each.contains("ON point")), report);
        assertTrue(owed.stream().anyMatch(each -> each.contains("OFF point")), report);
    }

    @Test
    void aBoundWrittenWrongInTheSecondTableIsShownByNoRowOfTheFirst() {
        String wrong = ALIKE.replace("100", "1000");
        String report = reportOf(model(wrong, TWO_TABLES) + HEAD + rowsThrough(true));
        List<String> owed = owedAtTheComparison(report);
        assertTrue(owed.stream().anyMatch(each -> each.contains("ON point")), report);
    }

    @Test
    void rowsThroughBothTablesLeaveNothingOwed() {
        String report = reportOf(model(ALIKE, TWO_TABLES) + HEAD + rowsThrough(true)
                + rowsThrough(false));
        assertEquals(List.of(), owedAtTheComparison(report), report);
    }

    @Test
    void theSameTableReachedFromTwoCallsIsOneLine() {
        String report = reportOf(model(ALIKE,
                "if useFirst then gradeIn(first, a.v) else gradeIn(first, a.v)") + HEAD
                + rowsThrough(true));
        assertEquals(List.of(), owedAtTheComparison(report), report);
    }

    @Test
    void theSameTableUnderAnotherNameIsOneLine() {
        String report = reportOf(model(ALIKE,
                "{ let alias = first\n        if useFirst then gradeIn(first, a.v)"
                        + " else gradeIn(alias, a.v) }")
                + HEAD + rowsThrough(true));
        assertEquals(List.of(), owedAtTheComparison(report), report);
    }

    @Test
    void aTotalLookedUpInTwoTablesOwesTheBoundOfEach() {
        String source = model(ALIKE, TWO_TABLES)
                .replace("behavior f : (a: N, useFirst: Bool) -> Int",
                        "behavior f : (a: N, b: N, useFirst: Bool) -> Int")
                .replace("let f (a, useFirst) =", "let f (a, b, useFirst) =")
                .replace("gradeIn(first, a.v)", "gradeIn(first, a.v + b.v)")
                .replace("gradeIn(second, a.v)", "gradeIn(second, a.v + b.v)");
        String throughFirst = reportOf(source + HEAD + """
                    | (N { v = 100 }, N { v = 0 }, true) -> 2
                    | (N { v = 99 }, N { v = 0 }, true) -> 1
                    | (N { v = 101 }, N { v = 0 }, true) -> 2
                    | (N { v = 98 }, N { v = 0 }, true) -> 1
                """);
        assertTrue(throughFirst.contains("the bound is read out of second"), throughFirst);
        assertTrue(!throughFirst.contains("the bound is read out of first"), throughFirst);
    }

    private static String limitsModel(String call) {
        return """
                module demo

                data N = { v: Int }
                    invariant v >= 0
                data Limits = { max: Int }
                let low: Limits = Limits { max = 100 }
                let high: Limits = Limits { max = 100 }
                let within (limits: Limits, m: Int): Int = if m <= limits.max then 1 else 0

                behavior g : (a: N, useLow: Bool) -> Int

                let g (a, useLow) =
                    %s

                example g
                    | (N { v = 100 }, true) -> 1
                    | (N { v = 101 }, true) -> 0
                    | (N { v = 99 }, true) -> 1
                    | (N { v = 98 }, true) -> 1
                """.formatted(call);
    }

    @Test
    void theBoundsOfTwoRecordsAHelperIsGivenAreTwoLinesAsTablesAre() {
        String report = reportOf(
                limitsModel("if useLow then within(low, a.v) else within(high, a.v)"));
        List<String> owed = owedAtTheComparison(report);
        assertEquals(1, owed.stream().filter(each -> each.contains("ON point")).count(), report);
        assertEquals(1, owed.stream().filter(each -> each.contains("OFF point")).count(), report);
        assertTrue(report.contains("= 100 in within@13:42, the bound is read out of high"),
                report);
    }

    @Test
    void oneRecordGivenFromTwoCallsIsOneLine() {
        String report = reportOf(
                limitsModel("if useLow then within(low, a.v) else within(low, a.v)"));
        assertEquals(List.of(), owedAtTheComparison(report).stream()
                .filter(each -> each.contains("ON point") || each.contains("OFF point"))
                .toList(), report);
    }

    @Test
    void theDocumentTellsTheTwoTablesApart() {
        Compilation compilation = Compilation.ofSource(
                model(ALIKE, TWO_TABLES) + HEAD + rowsThrough(true), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(json.contains("held_in"), json);
    }

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("1 behavior:"), "the model was measured: " + report);
        return report;
    }
}
