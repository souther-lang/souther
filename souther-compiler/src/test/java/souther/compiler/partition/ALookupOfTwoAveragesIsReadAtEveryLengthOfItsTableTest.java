package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A lookup of two averages is read at every length of its table or at none: whether a month is
 * left unread does not follow where the readings of one condition ran out.
 *
 * <p>The lookup compares each row with two averages of months two filters keep. The ways the two
 * filters keep their months multiply at every row, so the condition that compares a row with an
 * average runs out of the readings of one condition at every length. What a fork over it is left
 * stating is not read off what was got to before that ({@link WhatAForkTests.PartsRead}): the
 * comparison that states it says what stopped it, and a fork of the lookup states nothing more.
 */
class ALookupOfTwoAveragesIsReadAtEveryLengthOfItsTableTest {

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
                data Month = { days: Days, pay: Yen }
                data Window = { a1: Month, a2: Month, b1: Month, b2: Month }
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
                    let pa = payableOf([ w.a1, w.a2 ])
                    let pb = payableOf([ w.b1, w.b2 ])
                    guard List.length(pa) >= 1 else NoPayable { nothing = 0 }
                    guard List.length(pb) >= 1 else NoPayable { nothing = 1 }
                    Decision { grade = gradeRowFor(averageOf(pa), averageOf(pb)).grade }
                }
                """.formatted(table);
    }

    /**
     * The same lookup with the second average compared beside a count over a closure of its own:
     * how many elements of {@code w.xs} hold a list containing nought. That count is a part of
     * what the comparison states that no reader of the values answers for.
     */
    private static String sourceBesideAClosure(int rows) {
        return replaced(replaced(replaced(replaced(source(rows),
                "b2: Month }", "b2: Month, xs: List<List<Int>> }"),
                "(ma: Yen, mb: Yen): Row =", "(ma: Yen, mb: Yen, n: Int): Row ="),
                "mb <= r.upperBound then", "mb.value + n <= r.upperBound.value then"),
                "gradeRowFor(averageOf(pa), averageOf(pb)).grade",
                "gradeRowFor(averageOf(pa), averageOf(pb),"
                        + " List.length(List.filter(ys -> List.allDistinctBy(k -> k, ys), w.xs))).grade");
    }

    private static String replaced(String in, String what, String with) {
        assertTrue(in.contains(what), what);
        return in.replace(what, with);
    }

    /** Everything the report leaves unread, with why and at which figure. */
    private static List<String> unread(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(compilation);
        List<String> out = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each :
                AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            each.partition().notRead().forEach(one -> out.add(
                    one.at() + " " + one.reason() + " " + one.figures()));
        }
        return out.stream().sorted().toList();
    }

    /**
     * A length at which the comparison of a row with an average runs out of the readings of one
     * condition leaves no month unread.
     *
     * <p>A reading that stopped hands the fork over the comparison no parts, so which months are
     * unread does not turn on where it stopped, and so not on the length. One length at which it
     * stops stands for them all.
     */
    @Test
    void noLengthOfTheTableLeavesAMonthUnreadThatAnotherLengthDoesNot() {
        assertEquals(List.of(), unread(source(2)),
                "what is left unread at a length the reading runs out at");
    }

    /**
     * And what the comparison states beside the average is not lost at the lengths that run out.
     *
     * <p>The count over the closure is nothing a reader of the values answers for, so the report
     * says it was not read, and says the same at every length. A length at which the reading ran
     * out of readings must not be one at which that goes unsaid, nor one that says more.
     */
    @Test
    void aPartOfTheComparisonNoReaderAnswersForIsSaidAtEveryLengthOfTheTable() {
        Map<Integer, List<String>> unreadByRows = new TreeMap<>();
        for (int rows : new int[] {2, 3}) {
            unreadByRows.put(rows, unread(sourceBesideAClosure(rows)));
        }

        assertEquals(unreadByRows.get(3), unreadByRows.get(2),
                "what is left unread does not follow the rows of the table");
        assertTrue(unreadByRows.get(2).stream().anyMatch(each -> each.startsWith("w.xs ")),
                "the count over the closure is said to be unread: " + unreadByRows.get(2));
    }
}
