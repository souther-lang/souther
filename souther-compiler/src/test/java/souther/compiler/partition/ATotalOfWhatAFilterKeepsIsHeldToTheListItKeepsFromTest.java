package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total over what a filter keeps of a list written out holds no more elements than that list,
 * however the kept list reaches the total: by a name, through a helper, or under a map. Each element
 * bounded, the total lies within an {@code Int} and a comparison of the total divided by the count
 * is read as the same comparison multiplied out is. With the elements unbounded the total can pass
 * an {@code Int}, and the run that gets there is said to stop.
 */
class ATotalOfWhatAFilterKeepsIsHeldToTheListItKeepsFromTest {

    private static final String SOURCE = """
            module k4

            data Yen = Int
                invariant value >= 0%s
            data Days = Int
                invariant value >= 0 && value <= 31
            data Month = { pay: Yen, days: Days }
            data NoMonth = { why: Int }

            let keptOf (a: Month, b: Month, c: Month): List<Month> =
                List.filter(m -> m.days.value >= 17, [a, b, c])

            behavior decide : (a: Month, b: Month, c: Month) -> Int | NoMonth

            let decide (a, b, c) = {
                let ms = %s
                guard List.length(ms) >= 1 else NoMonth { why = 0 }
                if %s >= 200 then 2 else 1
            }
            """;

    private static final String BOUNDED = " && value <= 1000000000000";

    private static final String FILTERED_HERE = "List.filter(m -> m.days.value >= 17, [a, b, c])";

    private static final String TOTAL = "List.sum(List.map(m -> m.pay.value, ms))";

    /** The report of the model, line by line. */
    private static List<String> report(String bound, String kept, String compared) {
        Compilation compilation = Compilation.ofSource(SOURCE.formatted(bound, kept, compared),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .toList();
    }

    private static List<String> unread(List<String> report) {
        return report.stream().filter(line -> line.contains("not read:")).toList();
    }

    /** The lines that say a run may stop, resolved or not. */
    private static List<String> stops(List<String> report) {
        return report.stream().filter(line -> line.contains("· stop")).toList();
    }

    private static final String FOLDED = "List.fold((acc, m) -> acc + m.pay.value, 0, ms)"
            + " / List.length(ms)";

    @ParameterizedTest
    @ValueSource(strings = {
            TOTAL + " / List.length(ms)",
            "Rational.toInt(DOWN, " + TOTAL + " / List.length(ms))",
    })
    void aComparisonOverTheFilteredTotalIsRead(String compared) {
        List<String> report = report(BOUNDED, FILTERED_HERE, compared);
        assertEquals(List.of(), unread(report));
        assertEquals(List.of(), stops(report));
        assertTrue(complete(report, "k4"), () -> String.join("\n", report));
    }

    /** A walk carrying a total over the kept list takes as many steps as the list it keeps from,
     *  so no step of it passes an {@code Int}. What the walk answers is no form the comparison
     *  reads, which is another matter than whether it stops. */
    @Test
    void aWalkOverTheFilteredListIsShownToStopNowhere() {
        assertEquals(List.of(), stops(report(BOUNDED, FILTERED_HERE, FOLDED)));
    }

    /** The kept list is what a helper answers, or a map of it. */
    @ParameterizedTest
    @ValueSource(strings = {
            "keptOf(a, b, c)",
            "List.map(m -> m, " + FILTERED_HERE + ")",
            "{ let all = [a, b, c]\n        List.filter(m -> m.days.value >= 17, all) }",
            // An element built here stands at no place, and holds what the rules of its type
            // leave it, whatever made it.
            "List.filter(m -> m.days.value >= 17, [a, b, Month { pay = Yen(5), days = Days(20) }])",
    })
    void theFilteredListReachedAnotherWayIsRead(String kept) {
        List<String> report = report(BOUNDED, kept, TOTAL + " / List.length(ms)");
        assertEquals(List.of(), unread(report));
        assertTrue(complete(report, "k4"), () -> String.join("\n", report));
    }

    /** The model of the report, as it was written, with its four rows. */
    private static final String AS_REPORTED = """
            module k4

            data Yen = Int
                invariant value >= 0 && value <= 1000000000000
            data Days = Int
                invariant value >= 0 && value <= 31
            data Month = { pay: Yen, days: Days }
            data NoMonth = { why: Int }

            behavior decide : (a: Month, b: Month, c: Month) -> Int | NoMonth

            let decide (a, b, c) = {
                let ms = List.filter(m -> m.days.value >= 17, [a, b, c])
                guard List.length(ms) >= 1 else NoMonth { why = 0 }
                if %s >= 200 then 2 else 1
            }

            example decide
                | "low"  : (Month { pay = Yen(50), days = Days(20) }, Month { pay = Yen(50), days = Days(20) }, Month { pay = Yen(50), days = Days(20) }) -> 1
                | "high" : (Month { pay = Yen(250), days = Days(20) }, Month { pay = Yen(250), days = Days(20) }, Month { pay = Yen(250), days = Days(20) }) -> 2
                | "one"  : (Month { pay = Yen(250), days = Days(20) }, Month { pay = Yen(50), days = Days(10) }, Month { pay = Yen(50), days = Days(10) }) -> 2
                | "none" : (Month { pay = Yen(250), days = Days(10) }, Month { pay = Yen(50), days = Days(10) }, Month { pay = Yen(50), days = Days(10) }) -> NoMonth { why = 0 }
            """;

    /** The model as it was reported, and its form rounding the average down, are measured
     *  complete: what the report was about. */
    @ParameterizedTest
    @ValueSource(strings = {
            TOTAL + " / List.length(ms)",
            "Rational.toInt(DOWN, " + TOTAL + " / List.length(ms))",
    })
    void theModelAsReportedIsMeasuredComplete(String compared) {
        Compilation compilation = Compilation.ofSource(AS_REPORTED.formatted(compared), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        List<String> report = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .toList();
        assertTrue(report.stream().anyMatch(line -> line.startsWith("k4")
                && line.endsWith("measurement: complete")), () -> String.join("\n", report));
    }

    private static final String BUILT_BY_A_HELPER = """
            module k5

            data Yen = Int
                invariant value >= 0 && value <= 1000000000000
            data Days = Int
                invariant value >= 0 && value <= 31
            data Pay = { base: Yen, extra: Yen }
            data Month = { pay: Pay, days: Days }
            data NoMonth = { why: Int }

            let totalOf (p: Pay): %s

            behavior decide : (a: Month, b: Month, c: Month) -> Int | NoMonth

            let decide (a, b, c) = {
                let ms = List.filter(m -> m.days.value >= 17, [a, b, c])
                guard List.length(ms) >= 1 else NoMonth { why = 0 }
                if List.sum(List.map(m -> totalOf(m.pay)%s, ms)) / List.length(ms) >= 200
                then 2 else 1
            }
            """;

    /** The report of the model where a helper works each month's amount out, as {@code helper}
     *  declares and answers it and {@code read} reads it off what it answers. */
    private static List<String> reportOfTheHelper(String helper, String read) {
        Compilation compilation = Compilation.ofSource(
                BUILT_BY_A_HELPER.formatted(helper, read), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .toList();
    }

    /** Whether {@code report} says its module is measured complete. */
    private static boolean complete(List<String> report, String module) {
        return report.stream().anyMatch(line -> line.startsWith(module)
                && line.endsWith("measurement: complete"));
    }

    /**
     * A helper that builds an amount of two, each at most the most an amount holds, may be
     * refused the build: their sum passes it. What the field of the amount built comes to is read
     * all the same, and the total over the months with it, but the build is no operation that
     * ends no run: a run evaluating the comparison may stop there, and the model is not measured
     * complete. The control works the same sum out as a whole number and builds nothing, and is.
     */
    @Test
    void aBuildThatMayBeRefusedKeepsTheModelFromBeingComplete() {
        List<String> built = reportOfTheHelper("Yen = p.base + p.extra", ".value");
        assertFalse(complete(built, "k5"), () -> String.join("\n", built));
        assertFalse(unread(built).isEmpty() && stops(built).isEmpty(),
                () -> String.join("\n", built));
        List<String> worked = reportOfTheHelper("Int = p.base.value + p.extra.value", "");
        assertTrue(complete(worked, "k5"), () -> "control\n" + String.join("\n", worked));
    }

    /** Control: with each amount unbounded above the total of three passes an {@code Int}, and
     *  the run that gets there is said to stop. */
    @ParameterizedTest
    @ValueSource(strings = {TOTAL + " / List.length(ms)", FOLDED})
    void withTheAmountsUnboundedTheTotalIsSaidToStop(String compared) {
        assertFalse(stops(report("", FILTERED_HERE, compared)).isEmpty());
    }
}
