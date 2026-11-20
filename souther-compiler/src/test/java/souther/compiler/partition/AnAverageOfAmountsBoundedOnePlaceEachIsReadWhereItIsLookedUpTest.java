package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
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

    /** The report of the model, line by line. */
    private static List<String> report(String bounds, String helpers, String looked) {
        Compilation compilation = Compilation.ofSource(
                SOURCE.formatted(bounds, helpers, looked), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines().toList();
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

    private static final String THE_MONTHS_A_FILTER_KEPT =
            "List.filter(p -> p.base > Yen(0), [ w.first, w.second, w.third ])";

    /**
     * The months are the ones a filter kept of three written: what each is handed is the place one
     * of the three stands at, whichever the filter kept, so the sum of what a month comes to is
     * asked of each place, as with no filter.
     */
    @Test
    void anAverageOfTheMonthsAFilterKeptIsRead() {
        for (String month : List.of("p.base.value + p.extra.value", "totalOf(p).value")) {
            String looked = """
                    Yen(Rational.toInt(DOWN,
                        List.sum(List.map(p -> %s, %s)) / 3))""".formatted(month,
                    THE_MONTHS_A_FILTER_KEPT);
            assertEquals(List.of(), unread(BOUNDS, "", looked), month);
        }
    }

    private static final String THE_MONTHS_ARE_FILTERED_AFTER_A_GUARD = """
            module demo

            data Yen = Int
                invariant value >= 0
            data Pay = { base: Yen, extra: Yen }
                %1$s
            data Month = { pay: Pay, days: Int }
            data Window = { first: Month, second: Month, third: Month }
            data Row = { grade: Int, lowerBound: Yen }
            data Decision = { grade: Int }
            data NoMonth = { n: Int }
            let table: List<Row> = [
                Row { grade = 1, lowerBound = Yen(0) },
                Row { grade = 2, lowerBound = Yen(100) } ]
            let totalOf (p: Pay): Yen = p.base + p.extra
            let gradeRowFor (m: Yen): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { grade = 0, lowerBound = Yen(0) }, table)
            let monthsOf (w: Window): List<Month> = [ w.first, w.second, w.third ]
            let payableOf (w: Window): List<Month> =
                List.filter(r -> %2$s, monthsOf(w))
            let averageOf (records: List<Month>): Yen =
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(r -> %3$s, records))
                        / List.length(records)))

            behavior f : (w: Window) -> Decision | NoMonth
                constructs Decision, Row, Yen, NoMonth
            let f (w) = {
                let payable = payableOf(w)
                guard List.length(payable) >= 1 else NoMonth { n = 0 }
                Decision { grade = gradeRowFor(averageOf(payable)).grade }
            }
            """;

    /** Whether the report says a run may end where nothing says so, of a model whose months are the
     *  ones a filter kept of three, averaged after a guard that one was kept. */
    private static boolean someStopIsLeftUntold(String bounds) {
        return someStopIsLeftUntold(bounds, "r.days >= 17");
    }

    /** The same, of the months a filter kept by {@code test}, which is written of {@code r}. */
    private static boolean someStopIsLeftUntold(String bounds, String test) {
        return someStopIsLeftUntold(bounds, test, "totalOf(r.pay).value");
    }

    /** The same, of a month that comes to {@code month}, which is written of {@code r}. */
    private static boolean someStopIsLeftUntold(String bounds, String test, String month) {
        Compilation compilation = Compilation.ofSource(
                THE_MONTHS_ARE_FILTERED_AFTER_A_GUARD.formatted(bounds, test, month), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .anyMatch(line -> line.contains("may end the run where nothing here says")
                        || line.contains("may stop a run"));
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

    @Test
    void theSameAverageWithNoBoundLeavesAStopUntold() {
        assertTrue(someStopIsLeftUntold(""));
    }

    /**
     * What decides which months are kept is worked out for each of the three, and is a stop of its
     * own: that the months it keeps total within an {@code Int} says nothing of whether it
     * answers.
     */
    @Test
    void aTestThatMayEndARunStillLeavesAStopUntoldWhereTheMonthsAreBounded() {
        assertTrue(someStopIsLeftUntold("""
                invariant base.value <= 1000000000000
                    invariant extra.value <= 1000000000000""",
                "r.pay.base.value + 9223372036854775807 > 0"));
    }

    /**
     * Three months of amounts up to a quintillion total within an {@code Int}, which twice as many
     * elements as an {@code Int} counts would not: it holds only where the most months there are
     * is three, however the list reached the total.
     */
    @Test
    void theMostMonthsThereAreIsThreeWhateverFilterKeptThem() {
        String bounds = """
                invariant base.value <= 1000000000000000000
                    invariant extra.value <= 1000000000000000000""";
        assertFalse(someStopIsLeftUntold(bounds));
        assertFalse(someStopIsLeftUntold(bounds, "r.days >= 17",
                "r.pay.base.value + r.pay.extra.value"));
    }

    /** Control: the same months with no bound on each amount can pass an {@code Int} in the total
     *  of a month or of the three, and a run stops there. */
    @Test
    void theMonthsAFilterKeptAreNotReadWithNoBound() {
        for (String month : List.of("p.base.value + p.extra.value", "totalOf(p).value")) {
            String looked = """
                    Yen(Rational.toInt(DOWN,
                        List.sum(List.map(p -> %s, %s)) / 3))""".formatted(month,
                    THE_MONTHS_A_FILTER_KEPT);
            assertFalse(unread("", "", looked).isEmpty(), month);
        }
    }

    /** Control: without a bound on each amount the total of two can pass the greatest
     *  {@code Int}, and a run stops there; bounded, none does. */
    @Test
    void theSameAverageOfAmountsWithNoBoundIsToldToStopWhereATotalPassesAnInt() {
        assertTrue(stopsWhereATotalPassesAnInt(report("", "", AVERAGE_WRITTEN_AT_THE_CALL)));
        assertFalse(stopsWhereATotalPassesAnInt(report(BOUNDS, "", AVERAGE_WRITTEN_AT_THE_CALL)));
    }

    /** Whether {@code report} says a run stops where the total of a month passes an {@code Int}. */
    private static boolean stopsWhereATotalPassesAnInt(List<String> report) {
        return report.stream().anyMatch(line -> line.contains("may stop a run")
                && line.contains("w.first.base + w.first.extra is at least 9223372036854775808"));
    }
}
