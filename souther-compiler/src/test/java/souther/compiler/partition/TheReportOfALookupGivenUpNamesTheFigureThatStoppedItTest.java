package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Figure;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A lookup whose reading runs out of the readings of one condition says the figure that stopped
 * it, at every month the rule over it is left unread, and never that the rule is about a derived
 * value.
 *
 * <p>The lookup compares each row with two averages of months two filters keep. Each average is
 * read once; the ways the two filters keep their months multiply at every row, so what each row
 * costs is its own however the averages are shared, and a table of a few rows is more than one
 * condition may read.
 *
 * <p>Which lengths run out is the reading's, and known: the test says where they are so that a
 * change to them is seen, and asks what is said where a length is given up.
 */
class TheReportOfALookupGivenUpNamesTheFigureThatStoppedItTest {

    private static String source(int rows) {
        StringBuilder table = new StringBuilder("let table: List<Row> = [\n");
        for (int i = 0; i < rows; i++) {
            table.append("    Row { grade = ").append(i + 1).append(", lowerBound = Yen(")
                    .append(i * 1000L).append("), upperBound = Yen(").append(i * 1000L + 999)
                    .append(") }").append(i + 1 < rows ? ",\n" : " ]\n");
        }
        return """
                module demo

                data Yen = Int
                    invariant value >= 0
                data Days = Int
                    invariant value >= 0 && value <= 31
                data Month = { days: Days, pay: Yen }
                data Window = { a1: Month, a2: Month, a3: Month, b1: Month, b2: Month, b3: Month }
                data Row = { grade: Int, lowerBound: Yen, upperBound: Yen }
                data Decision = { grade: Int }
                data NoPayable = { nothing: Int }
                %s
                let gradeRowFor (ma: Yen, mb: Yen): Row =
                    List.fold((acc, r) -> if r.lowerBound <= ma && mb <= r.upperBound then r else acc,
                              Row { grade = 0, lowerBound = Yen(0), upperBound = Yen(0) }, table)
                let payableOf (months: List<Month>): List<Month> =
                    List.filter(r -> r.days >= 17, months)
                let averageOf (records: List<Month>): Yen =
                    Yen(Rational.toInt(DOWN,
                        List.sum(List.map(r -> r.pay.value, records))
                        / List.length(records)))

                behavior f : (w: Window) -> Decision | NoPayable
                    constructs Decision, Row, Yen, NoPayable
                let f (w) = {
                    let pa = payableOf([ w.a1, w.a2, w.a3 ])
                    let pb = payableOf([ w.b1, w.b2, w.b3 ])
                    guard List.length(pa) >= 1 else NoPayable { nothing = 0 }
                    guard List.length(pb) >= 1 else NoPayable { nothing = 1 }
                    Decision { grade = gradeRowFor(averageOf(pa), averageOf(pb)).grade }
                }
                """.formatted(table);
    }

    private record Unread(String at, UndividedPosition.Reason reason, List<Figure> figures) {}

    /** What the report leaves unread at the months themselves, where a rule over an average is
     *  filed. */
    private static List<Unread> atTheMonths(int rows) {
        Compilation compilation = Compilation.ofSource(source(rows), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model under test compiles");
        List<Unread> out = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each :
                AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            each.partition().notRead().forEach(one -> {
                if (one.at().toString().matches("w\\.[ab][123]")) {
                    out.add(new Unread(one.at().toString(), one.reason(), one.figures()));
                }
            });
        }
        return out;
    }

    /**
     * Which lengths of the table run out is a known limit, and these are where it is.
     *
     * <p>Near what one condition may read, whether a length is read depends on how much each
     * reading is charged and in what order, and it is not monotone in the length: three rows get
     * through, four and five are given up, six get through. A change to how readings are charged
     * moves these, and is meant to move this test with it; it is written so that the movement is
     * seen, and not so that the lengths stay.
     *
     * <p>Where a length is given up, each month is left unread at the figure that stopped it, and
     * never as a rule about a derived value.
     */
    @Test
    void whereTheLengthsOfTheTableRunOutIsAKnownLimitAndTheFigureIsSaid() {
        Map<Integer, Integer> monthsUnread = new TreeMap<>();
        for (int rows : new int[] {3, 4, 5, 6}) {
            List<Unread> left = atTheMonths(rows);
            monthsUnread.put(rows, left.size());
            for (Unread each : left) {
                assertEquals(UndividedPosition.Reason.RULE_MEANING_NOT_READ, each.reason(),
                        rows + " rows at " + each.at());
                assertEquals(List.of(new Figure.Budget(
                                CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION)),
                        each.figures(), rows + " rows at " + each.at());
            }
        }

        assertEquals(Map.of(3, 0, 4, 3, 5, 3, 6, 0), monthsUnread,
                "rows given up, with how many of the three months are left unread");
    }
}
