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

/**
 * The average of the months a filter keeps, looked up in a table of lower bounds, is read for a
 * table longer than twelve rows.
 *
 * <p>Each row's {@code if} compares the same average, which the months a filter keeps decide. What
 * is read of those months, and of how many of them are kept, is the average's and the same at
 * every row; only the comparison with the row's bound is the row's. So the average is read once
 * and each row is charged for its own comparison, and the readings of one condition last for a
 * table as long as the statute writes.
 */
class TheLookupOfAFilteredAverageIsReadInATableOfAnyLengthTest {

    private static final String HEAD = """
            module demo

            data Yen = Int
                invariant value >= 0
            data Days = Int
                invariant value >= 0 && value <= 31
            data Month = { days: Days, pay: Yen }
            data Window = { first: Month, second: Month, third: Month }
            data Row = { grade: Int, lowerBound: Yen, upperBound: Yen }
            data Decision = { grade: Int }
            data NoPayable = { nothing: Int }
            """;

    private static final String TAIL = """
            let monthsOf (w: Window): List<Month> = [ w.first, w.second, w.third ]
            let payableOf (w: Window): List<Month> =
                List.filter(r -> r.days >= 17, monthsOf(w))
            let averageOf (records: List<Month>): Yen =
                Yen(Rational.toInt(DOWN,
                    List.sum(List.map(r -> r.pay.value, records))
                    / List.length(records)))

            behavior f : (w: Window) -> Decision | NoPayable
                constructs Decision, Row, Yen, NoPayable
            let f (w) = {
                let payable = payableOf(w)
                guard List.length(payable) >= 1 else NoPayable { nothing = 0 }
                Decision { grade = gradeRowFor(averageOf(payable)).grade }
            }
            """;

    /** The lookup of the average: the last row whose lower bound it reaches. */
    static final String ABOVE_THE_BOUND = """
            let gradeRowFor (m: Yen): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { grade = 0, lowerBound = Yen(0), upperBound = Yen(0) }, table)
            """;

    /** The same, asking of each row both of its bounds. */
    static final String BETWEEN_THE_BOUNDS = """
            let gradeRowFor (m: Yen): Row =
                List.fold((acc, r) -> if r.lowerBound <= m && m <= r.upperBound then r else acc,
                          Row { grade = 0, lowerBound = Yen(0), upperBound = Yen(0) }, table)
            """;

    /** A table of {@code rows} rows, each a thousand wide. */
    private static String table(int rows) {
        StringBuilder out = new StringBuilder("let table: List<Row> = [\n");
        for (int i = 0; i < rows; i++) {
            out.append("    Row { grade = ").append(i + 1).append(", lowerBound = Yen(")
                    .append(i * 1000).append("), upperBound = Yen(").append(i * 1000 + 999)
                    .append(") }").append(i + 1 < rows ? ",\n" : " ]\n");
        }
        return out.toString();
    }

    /** What the report leaves unread, as {@code position reason}, with the figures it says it
     *  stopped at. */
    record Unread(String at, UndividedPosition.Reason reason, List<Figure> figures) {}

    static List<Unread> unread(int rows, String lookup) {
        Compilation compilation = Compilation.ofSource(HEAD + table(rows) + lookup + TAIL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model under test compiles");
        List<Unread> out = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each :
                AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            each.partition().notRead().forEach(one ->
                    out.add(new Unread(one.at().toString(), one.reason(), one.figures())));
        }
        return out;
    }

    /** The positions the report leaves unread at the months themselves, which is where a rule
     *  about the average is filed. */
    static List<Unread> atTheMonths(List<Unread> all) {
        return all.stream().filter(one -> one.at().matches("w\\.(first|second|third)")).toList();
    }

    @Test
    void aTableOfThirteenRowsGivesUpNoRuleAboutTheMonths() {
        assertEquals(List.of(), atTheMonths(unread(13, ABOVE_THE_BOUND)),
                "the average is read once for all the rows, and thirteen of them are within what "
                        + "one condition may read");
    }

    /**
     * A lookup whose reading runs out of the readings of one condition is given up, and the
     * report says which figure.
     *
     * <p>Two comparisons at every row use up what one condition may read within a table of three
     * rows. What the rule over each month is left with is that figure, and never that the rule is
     * about a derived value, which is true of the rule whether or not a reading of it was made.
     */
    @Test
    void aReadingGivenUpSaysTheFigureThatStoppedIt() {
        List<Unread> months = atTheMonths(unread(3, BETWEEN_THE_BOUNDS));

        assertEquals(List.of("w.first", "w.second", "w.third"),
                months.stream().map(Unread::at).toList());
        for (Unread each : months) {
            assertEquals(UndividedPosition.Reason.RULE_MEANING_NOT_READ, each.reason(), each.at());
            assertEquals(List.of(new Figure.Budget(
                            CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION)),
                    each.figures(), each.at());
        }
    }
}
