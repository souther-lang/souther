package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

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

    /** The places the report says nothing is read of. */
    private static List<String> unread(String bounds, String helpers, String looked) {
        Compilation compilation = Compilation.ofSource(
                SOURCE.formatted(bounds, helpers, looked), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:"))
                .map(line -> line.replaceAll(".*about `([^`]*)`.*", "$1"))
                .toList();
    }

    @Test
    void anAverageOfMonthsWrittenAtTheLookupIsRead() {
        assertEquals(List.of(), unread(BOUNDS, "", AVERAGE_WRITTEN_AT_THE_CALL));
    }

    /** The months are what a helper answers: a list is written out where the helper's body writes
     *  it, with the parameter it was handed read as the value it was handed. */
    @Test
    void anAverageOfMonthsAHelperListsIsRead() {
        assertEquals(List.of(), unread(BOUNDS, MONTHS_HELPER, """
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(p -> totalOf(p).value, monthsOf(w))) / 3))"""));
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
