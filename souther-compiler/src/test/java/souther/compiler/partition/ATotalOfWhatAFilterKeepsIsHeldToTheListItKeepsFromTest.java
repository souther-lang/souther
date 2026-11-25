package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.ACompiledModel;
import souther.compiler.StopsTheReportSays;
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

    /** What every model here is measured at: the readings of its comparisons and stops, and no
     *  row looked for, which nothing here asks about. */
    private static final Adequacy.Asked READ = new Adequacy.Asked(Adequacy.Level.OFF, false);

    private static final String BOUNDED =" && value <= 1000000000000";

    private static final String FILTERED_HERE = "List.filter(m -> m.days.value >= 17, [a, b, c])";

    private static final String TOTAL = "List.sum(List.map(m -> m.pay.value, ms))";

    /** The report of the model, line by line. */
    private static List<String> report(String bound, String kept, String compared) {
        Compilation compilation = Compilation.ofSource(SOURCE.formatted(bound, kept, compared),
                "Main");
        compilation.measure(READ);
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .toList();
    }

    /** What the report of the same model says of its stops and of what it leaves unread, as its
     *  findings say it. */
    private static StopsTheReportSays.Said said(String bound, String kept, String compared) {
        Compilation compilation = Compilation.ofSource(SOURCE.formatted(bound, kept, compared),
                "Main");
        compilation.measure(READ);
        ACompiledModel.compiles(compilation);
        return StopsTheReportSays.of(compilation);
    }

    /** Whether a comparison is left unread for a run that may stop where nothing says. */
    private static boolean unreadForAStop(StopsTheReportSays.Said said) {
        return said.unread().stream()
                .anyMatch(each -> each.because().equals("evaluation_stops_not_fully_read"));
    }

    private static List<String> unread(List<String> report) {
        return report.stream().filter(line -> line.contains("not read:")).toList();
    }


    private static final String FOLDED = "List.fold((acc, m) -> acc + m.pay.value, 0, ms)"
            + " / List.length(ms)";

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
        compilation.measure(READ);
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

    /** The model where a helper works each month's amount out, as {@code helper} declares and
     *  answers it and {@code read} reads it off what it answers, measured. */
    private static Compilation compiledWithTheHelper(String helper, String read) {
        Compilation compilation = Compilation.ofSource(
                BUILT_BY_A_HELPER.formatted(helper, read), "Main");
        compilation.measure(READ);
        ACompiledModel.compiles(compilation);
        return compilation;
    }

    /** The report of {@code compilation} in English, line by line. */
    private static List<String> humanOf(Compilation compilation) {
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
     * all the same, and the total over the months with it, but the build is a step a run may stop
     * at, said there, and the model is not measured complete. The control works the same sum out
     * as a whole number and builds nothing, and is.
     */
    @Test
    void aBuildThatMayBeRefusedKeepsTheModelFromBeingComplete() {
        Compilation built = compiledWithTheHelper("Yen = p.base + p.extra", ".value");
        StopsTheReportSays.Said ofTheBuild = StopsTheReportSays.of(built);
        assertFalse(complete(humanOf(built), "k5"), ofTheBuild::toString);
        assertTrue(ofTheBuild.stops().stream().anyMatch(stop -> stop.subject().equals("k5.Yen")),
                ofTheBuild::toString);
        assertTrue(unreadForAStop(ofTheBuild), ofTheBuild::toString);

        Compilation worked = compiledWithTheHelper("Int = p.base.value + p.extra.value", "");
        StopsTheReportSays.Said ofTheSum = StopsTheReportSays.of(worked);
        assertTrue(complete(humanOf(worked), "k5"), () -> "control " + ofTheSum);
        assertEquals(List.of(), ofTheSum.stops(), "control");
    }

    /** Control: with each amount unbounded above the total of three passes an {@code Int}, and
     *  a stop in the sum of the three amounts is said of the run that gets there, shown or not
     *  resolved. */
    @Test
    void withTheAmountsUnboundedTheTotalIsSaidToStopInTheSumOfTheAmounts() {
        StopsTheReportSays.Said unbounded = said("", FILTERED_HERE, TOTAL + " / List.length(ms)");
        assertTrue(unbounded.stops().stream().flatMap(stop -> stop.operations().stream())
                .anyMatch(each -> "a.pay + b.pay + c.pay".equals(each.written())),
                unbounded::toString);
    }

    /** The same of a walk carrying the total, which takes as many steps as the list it keeps
     *  from: said to stop with the amounts unbounded, and with them bounded, where no step of it
     *  passes an {@code Int}, not. What the walk carries is told of no element, and the two
     *  differ in nothing but how far the amounts reach. */
    @Test
    void withTheAmountsUnboundedTheWalkIsSaidToStopAndBoundedNot() {
        assertFalse(said("", FILTERED_HERE, FOLDED).stops().isEmpty());
        assertEquals(List.of(), said(BOUNDED, FILTERED_HERE, FOLDED).stops(), "control");
    }
}
