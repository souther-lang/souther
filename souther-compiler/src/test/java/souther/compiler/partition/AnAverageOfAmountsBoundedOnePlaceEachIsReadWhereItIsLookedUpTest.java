package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.NotRead;
import souther.compiler.UnreadBesideItsStops;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The average of the amounts of several months, looked up in a table of lower bounds, is read when
 * each amount is bounded at the place it stands, however the months reach the average.
 *
 * <p>The average is a division of a total, rounded to a whole number and made an amount. It is an
 * amount the table can be asked of only if the total is shown to fit an {@code Int}, which turns on
 * the runs the declarations leave the amounts: bounded one place at a time, the total of fifteen of
 * them is far from the ends. Left unbounded the total can pass them, a run stops there, and that
 * stop is told with the amounts it turns on.
 */
class AnAverageOfAmountsBoundedOnePlaceEachIsReadWhereItIsLookedUpTest {

    private static final String SOURCE = """
            module demo

            data Yen = Int
                invariant value >= 0
            data Pay = { base: Yen, extra: Yen }
                %s
            data Window = { first: Pay, second: Pay, third: Pay }
            data Row = { grade: Int, lowerBound: Yen }
            data Decision = { grade: Int }
            let table: List<Row> = [
                Row { grade = 1, lowerBound = Yen(0) },
                Row { grade = 2, lowerBound = Yen(100) },
                Row { grade = 3, lowerBound = Yen(200) } ]
            let totalOf (p: Pay): Yen = p.base + p.extra
            let gradeRowFor (m: Yen): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { grade = 0, lowerBound = Yen(0) }, table)
            %s

            behavior f : (w: Window) -> Decision
                constructs Decision, Row, Yen
            let f (w) = Decision { grade = gradeRowFor(%s).grade }
            """;

    private static final String BOUNDS = """
            invariant base.value <= 1000000000000
                invariant extra.value <= 1000000000000""";

    private static final String AVERAGE_WRITTEN_AT_THE_CALL = """
            Yen(Rational.toInt(DOWN,
                List.sum(List.map(p -> totalOf(p).value, [ w.first, w.second, w.third ])) / 3))""";

    private static final String MONTHS_HELPER = """
            let monthsOf (w: Window): List<Pay> = [ w.first, w.second, w.third ]""";

    private static final String AVERAGE_HELPER = """
            let averageOf (records: List<Pay>): Yen =
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(p -> totalOf(p).value, records)) / List.length(records)))""";

    /** What each model was measured to, by what it is made of: a test that asks both which places
     *  are unread and where the borders are asks one model once. */
    private static final Map<List<String>, List<String>> REPORTS = new ConcurrentHashMap<>();

    /** The report of the model, line by line. */
    private static List<String> report(String bounds, String helpers, String looked) {
        return REPORTS.computeIfAbsent(List.of(bounds, helpers, looked), _ -> {
            Compilation compilation = Compilation.ofSource(
                    SOURCE.formatted(bounds, helpers, looked), "Main");
            compilation.measure(new Adequacy.Asked(Adequacy.Level.OFF, false));
            ACompiledModel.compiles(compilation);
            return AdequacyReport.of(compilation)
                    .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                    .toList();
        });
    }

    /** The places the report says nothing is read of. */
    private static List<String> unread(String bounds, String helpers, String looked) {
        return report(bounds, helpers, looked).stream()
                .filter(line -> line.contains("not read:"))
                .map(line -> line.replaceAll(".*about `([^`]*)`.*", "$1"))
                .toList();
    }

    private static final Pattern A_POINT_OF_THE_LOOKUP =
            Pattern.compile("read as f/.*: = (\\S+) in gradeRowFor");

    /**
     * The values of the average the lookup's borders are at: where it equals a lower bound of the
     * table, and where it is the least below it. That they are these is what reading the average
     * as a number of the amounts comes to, which no absence of a {@code not read} line says.
     */
    private static List<String> bordersOfTheLookup(String bounds, String helpers, String looked) {
        return report(bounds, helpers, looked).stream()
                .map(A_POINT_OF_THE_LOOKUP::matcher)
                .filter(Matcher::find)
                .map(found -> found.group(1))
                .sorted()
                .toList();
    }

    private static final List<String> THE_BORDERS_OF_THE_TABLE =
            List.of("100", "200", "299/3", "599/3");

    @Test
    void anAverageOfMonthsWrittenAtTheLookupIsRead() {
        assertEquals(List.of(), unread(BOUNDS, "", AVERAGE_WRITTEN_AT_THE_CALL));
        assertEquals(THE_BORDERS_OF_THE_TABLE,
                bordersOfTheLookup(BOUNDS, "", AVERAGE_WRITTEN_AT_THE_CALL));
    }

    /** The months are what a helper answers: a list is written out where the helper's body writes
     *  it, with the parameter it was handed read as the value it was handed. */
    @Test
    void anAverageOfMonthsAHelperListsIsRead() {
        String looked = """
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(p -> totalOf(p).value, monthsOf(w))) / 3))""";
        assertEquals(List.of(), unread(BOUNDS, MONTHS_HELPER, looked));
        assertEquals(THE_BORDERS_OF_THE_TABLE, bordersOfTheLookup(BOUNDS, MONTHS_HELPER, looked));
    }

    private static final String AVERAGE_OVER_THE_HELPERS_MONTHS = """
            Yen(Rational.toInt(DOWN,
                List.sum(List.map(p -> totalOf(p).value, monthsOf(w))) / 3))""";

    /** A {@code let} before the list works nothing out that can stop a run: the months are the same
     *  list, and are read as they are without it. */
    @Test
    void aHelperThatBindsAValueBeforeItsListIsRead() {
        String helper = """
                let monthsOf (w: Window): List<Pay> = {
                    let first = w.first
                    [ first, w.second, w.third ]
                }""";
        assertEquals(List.of(), unread(BOUNDS, helper, AVERAGE_OVER_THE_HELPERS_MONTHS));
        assertEquals(THE_BORDERS_OF_THE_TABLE,
                bordersOfTheLookup(BOUNDS, helper, AVERAGE_OVER_THE_HELPERS_MONTHS));
    }

    /**
     * A {@code let} before the list whose value can pass the ends of an {@code Int} is worked out
     * all the same, whether or not the list reads it: a run stops there, and the months the list
     * names are not all the runs that get to the lookup. The list a helper answers is the same
     * list as in the test above.
     */
    @Test
    void aHelperThatWorksOutAValueThatCanStopBeforeItsListIsNotRead() {
        String helper = """
                let monthsOf (w: Window): List<Pay> = {
                    let unused = w.first.base.value + 9223372036854775807
                    [ w.first, w.second, w.third ]
                }""";
        assertFalse(unread(BOUNDS, helper, AVERAGE_OVER_THE_HELPERS_MONTHS).isEmpty());
    }

    /** The same where the list is written at the lookup and not answered by a helper. */
    @Test
    void aListWrittenAfterAValueThatCanStopIsNotRead() {
        assertFalse(unread(BOUNDS, "", """
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(p -> totalOf(p).value, {
                        let unused = w.first.base.value + 9223372036854775807
                        [ w.first, w.second, w.third ]
                    })) / 3))""").isEmpty());
    }

    /** And where the list is only counted. */
    @Test
    void aListCountedAfterAValueThatCanStopIsNotRead() {
        String helper = """
                let monthsOf (w: Window): List<Pay> = {
                    let unused = w.first.base.value + 9223372036854775807
                    [ w.first, w.second, w.third ]
                }""";
        assertFalse(unread(BOUNDS, helper, """
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(p -> totalOf(p).value, [ w.first, w.second, w.third ]))
                        / List.length(monthsOf(w))))""").isEmpty());
    }

    /** A rounding in a helper is handed its policy by a name, which stands at the case it was
     *  handed: the way it rounds is the same as when the case is written at the call. */
    @Test
    void aRoundingAHelperIsHandedItsPolicyToIsRead() {
        String helper = """
                let roundedWith (mode: RoundingMode, x: Rational): Int = Rational.toInt(mode, x)""";
        String looked = """
                Yen(roundedWith(DOWN,
                    List.sum(List.map(p -> totalOf(p).value, [ w.first, w.second, w.third ])) / 3))""";
        assertEquals(List.of(), unread(BOUNDS, helper, looked));
        assertEquals(THE_BORDERS_OF_THE_TABLE, bordersOfTheLookup(BOUNDS, helper, looked));
    }

    /** The average is a helper's, handed the list a second helper answers, and divides by the
     *  length of the list it was handed. */
    @Test
    void anAverageAHelperTakesTheListOfAnotherHelperToIsRead() {
        assertEquals(List.of(), unread(BOUNDS, MONTHS_HELPER + "\n" + AVERAGE_HELPER,
                "averageOf(monthsOf(w))"));
    }

    private static final String THE_MONTHS_ARE_FILTERED_AFTER_A_GUARD = """
            module demo

            data Yen = Int
                invariant value >= 0
            data Pay = { base: Yen, extra: Yen }
                %1$s
            data Month = { pay: Pay, days: Int }
            data Window = { first: Month, second: Month, third: Month }
            data Done = { n: Int }
            data NoMonth = { n: Int }
            let totalOf (p: Pay): Yen = p.base + p.extra
            let monthsOf (w: Window): List<Month> = [ w.first, w.second, w.third ]
            let payableOf (w: Window): List<Month> =
                List.filter(r -> r.days >= 17, monthsOf(w))
            let averageOf (records: List<Month>): Yen =
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(r -> totalOf(r.pay).value, records))
                        / List.length(records)))

            behavior f : (w: Window) -> Done | NoMonth
                constructs Done, Yen, NoMonth
            let f (w) = {
                let payable = payableOf(w)
                guard List.length(payable) >= 1 else NoMonth { n = 0 }
                guard averageOf(payable) >= Yen(100) else NoMonth { n = 1 }
                Done { n = 1 }
            }
            """;

    /** Whether the reading of that model leaves a comparison unread for a run that may stop where
     *  nothing says, the months' amounts held by {@code bounds}. */
    private static boolean someStopIsLeftUntold(String bounds) {
        Compilation compilation = Compilation.ofSource(
                THE_MONTHS_ARE_FILTERED_AFTER_A_GUARD.formatted(bounds), "Main");
        compilation.measure(new Adequacy.Asked(Adequacy.Level.OFF, false));
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .anyMatch(line -> NotRead.isOne(line)
                        && line.contains(UnreadBesideItsStops.STOPS_NOT_ALL_TOLD));
    }

    /**
     * The months reach the average through a helper that is handed what another helper answered,
     * which the inliner leaves as a {@code let} around the filter: each month is still one of the
     * three written, and the total of them is within an {@code Int}.
     */
    @Test
    void anAverageOfTheMonthsAFilterKeptAfterAGuardLeavesNoStopUntold() {
        assertFalse(someStopIsLeftUntold("""
                invariant base.value <= 1000000000000
                    invariant extra.value <= 1000000000000"""));
    }

    /** And the comparison of that average is read: the total is over no more months than the
     *  three the filter keeps from, each bounded, so it lies within an {@code Int}. */
    @Test
    void anAverageOfTheMonthsAFilterKeptAfterAGuardIsRead() {
        Compilation compilation = Compilation.ofSource(
                THE_MONTHS_ARE_FILTERED_AFTER_A_GUARD.formatted("""
                        invariant base.value <= 1000000000000
                            invariant extra.value <= 1000000000000"""), "Main");
        compilation.measure(new Adequacy.Asked(Adequacy.Level.OFF, false));
        ACompiledModel.compiles(compilation);
        assertEquals(List.of(), AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:")).toList());
    }

    @Test
    void theSameAverageWithNoBoundLeavesAStopUntold() {
        assertTrue(someStopIsLeftUntold(""));
    }

    /** Control: without a bound on each amount the total of two can pass the greatest
     *  {@code Int}, and a run getting there stops; bounded, none does. The stop is said at the
     *  addition in the helper, read on the month it is applied to, with the rows it turns on —
     *  and what the amount built there asks is said of the month as well, and of no name the
     *  helper's body stands in for it. */
    @Test
    void theSameAverageOfAmountsWithNoBoundIsSaidToStopWhereATotalPassesAnInt() {
        List<String> unbounded = report("", "", AVERAGE_WRITTEN_AT_THE_CALL);
        assertTrue(stopsWhereATotalPassesAnInt(unbounded));
        assertTrue(unbounded.stream().noneMatch(line -> line.contains("INLINER")),
                () -> String.join("\n", unbounded));
        assertFalse(stopsWhereATotalPassesAnInt(report(BOUNDS, "", AVERAGE_WRITTEN_AT_THE_CALL)));
    }

    /** Whether {@code report} says a run that gets there stops where the total of a month passes
     *  an {@code Int}. */
    private static boolean stopsWhereATotalPassesAnInt(List<String> report) {
        return report.stream().anyMatch(line -> line.contains("may stop a run:")
                && line.contains("w.first.base + w.first.extra is at least 9223372036854775808"));
    }
}
