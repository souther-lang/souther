package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Figure;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
 * <p>Which length runs out is the reading's and not this test's to say. It takes the first length
 * of a few that leaves a month unread and asks what is said there, and that there is one, so that
 * it asks nothing only if the reading ever gets through them all.
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

    @Test
    void aMonthLeftUnreadNamesTheFigureAndNeverADerivedValue() {
        List<Unread> left = List.of();
        int rows = 2;
        while (left.isEmpty() && rows < 8) {
            left = atTheMonths(++rows);
        }
        assertTrue(!left.isEmpty(), "some length of the table is more than one condition may read");
        for (Unread each : left) {
            assertEquals(UndividedPosition.Reason.RULE_MEANING_NOT_READ, each.reason(),
                    rows + " rows at " + each.at());
            assertEquals(List.of(new Figure.Budget(
                            CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION)),
                    each.figures(), rows + " rows at " + each.at());
        }
    }
}
