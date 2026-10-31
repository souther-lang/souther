package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Figure;
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

    /** A table of {@code rows} rows, each a thousand wide. */
    private static String table(int rows) {
        long[] bounds = new long[rows];
        for (int i = 0; i < rows; i++) {
            bounds[i] = i * 1000L;
        }
        return table(bounds);
    }

    /** A table with a row for each of {@code bounds}, as the lower bound of the row and a
     *  thousand above it as its upper. */
    private static String table(long[] bounds) {
        StringBuilder out = new StringBuilder("let table: List<Row> = [\n");
        for (int i = 0; i < bounds.length; i++) {
            out.append("    Row { grade = ").append(i + 1).append(", lowerBound = Yen(")
                    .append(bounds[i]).append("), upperBound = Yen(").append(bounds[i] + 999)
                    .append(") }").append(i + 1 < bounds.length ? ",\n" : " ]\n");
        }
        return out.toString();
    }

    /** What the report leaves unread, as {@code position reason}, with the figures it says it
     *  stopped at. */
    record Unread(String at, UndividedPosition.Reason reason, List<Figure> figures) {}

    static List<Unread> unread(int rows, String lookup) {
        return unread(table(rows), lookup);
    }

    private static List<Unread> unread(String table, String lookup) {
        Compilation compilation = Compilation.ofSource(HEAD + table + lookup + TAIL, "Main");
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

    /**
     * One row more is more of the same comparison and no other thing to say: the report of a table
     * the readings of one condition were always enough for is the report of one row longer.
     */
    @Test
    void aTableOneRowLongerIsReportedTheSame() {
        assertEquals(unread(12, ABOVE_THE_BOUND), unread(13, ABOVE_THE_BOUND));
    }

    /**
     * Bounds that are out of order, and one that two rows have, are each row's own comparison with
     * the average, which the rows share: the last row whose bound the average reaches is another
     * row, and reading it is no cheaper or dearer for that.
     */
    @Test
    void aTableOutOfOrderWithARepeatedBoundIsReadAsWell() {
        long[] bounds = {3000, 0, 1000, 1000, 7000, 2000, 5000, 4000, 6000, 8000, 9000, 10000, 3000};

        assertEquals(List.of(), atTheMonths(unread(table(bounds), ABOVE_THE_BOUND)));
    }

    @Test
    void aTableOfThirteenRowsGivesUpNoRuleAboutTheMonths() {
        assertEquals(List.of(), atTheMonths(unread(13, ABOVE_THE_BOUND)),
                "the average is read once for all the rows, and thirteen of them are within what "
                        + "one condition may read");
    }
}
