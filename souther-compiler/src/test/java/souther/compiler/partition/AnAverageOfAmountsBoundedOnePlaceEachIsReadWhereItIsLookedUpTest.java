package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * The average of the amounts of several months, looked up in a table of lower bounds, is read when
 * each amount is bounded at the place it stands, however the months reach the average.
 *
 * <p>The average is a division of a total, rounded to a whole number and made an amount. It is an
 * amount the table can be asked of only if the total is shown to fit an {@code Int}, which turns on
 * the runs the declarations leave the amounts: bounded one place at a time, the total of fifteen of
 * them is far from the ends. Left unbounded the total can pass them, a run stops there, and the
 * lookup is not read.
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
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines().toList();
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

    /** Control: without a bound on each amount the total of six can pass the greatest {@code Int},
     *  a run stops there, and which amounts settle the lookup is not worked out. */
    @Test
    void theSameAverageOfAmountsWithNoBoundIsNotRead() {
        assertFalse(unread("", "", AVERAGE_WRITTEN_AT_THE_CALL).isEmpty());
    }
}
