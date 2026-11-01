package souther.compiler.partition;

import org.junit.jupiter.api.Test;

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

    /**
     * The same lookup with the second average compared beside a count over a closure of its own:
     * how many elements of {@code w.xs} hold a list containing nought. That count is a part of
     * what the comparison states that no reader of the values answers for.
     */
    private static String sourceBesideAClosure(int rows) {
        return replaced(replaced(replaced(replaced(source(rows),
                "b3: Month }", "b3: Month, xs: List<List<Int>> }"),
                "(ma: Yen, mb: Yen): Row =", "(ma: Yen, mb: Yen, n: Int): Row ="),
                "mb <= r.upperBound then", "mb.value + n <= r.upperBound.value then"),
                "gradeRowFor(averageOf(pa), averageOf(pb)).grade",
                "gradeRowFor(averageOf(pa), averageOf(pb),"
                        + " List.length(List.filter(ys -> List.contains(0, ys), w.xs))).grade");
    }

    private static String replaced(String in, String what, String with) {
        assertTrue(in.contains(what), what);
        return in.replace(what, with);
    }

    /** Everything the report leaves unread, with why and at which figure. */
    private static List<String> unread(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model under test compiles");
        List<String> out = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each :
                AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            each.partition().notRead().forEach(one -> out.add(
                    one.at() + " " + one.reason() + " " + one.figures()));
        }
        return out.stream().sorted().toList();
    }

    /**
     * The lengths between the three rows that were read and the six that were, which the
     * comparison of a row with an average runs out of the readings of one condition at, leave no
     * month unread either.
     *
     * <p>Where the parts a fork over the comparison turns on were taken from what the stopped
     * reading got to, four and five rows left the three months of one average unread, and three
     * and six did not.
     */
    @Test
    void noLengthOfTheTableLeavesAMonthUnreadThatAnotherLengthDoesNot() {
        Map<Integer, List<String>> unreadByRows = new TreeMap<>();
        for (int rows : new int[] {4, 5}) {
            unreadByRows.put(rows, unread(source(rows)));
        }

        assertEquals(Map.of(4, List.of(), 5, List.of()), unreadByRows,
                "what is left unread, by the rows of the table");
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
        for (int rows : new int[] {4, 6}) {
            unreadByRows.put(rows, unread(sourceBesideAClosure(rows)));
        }

        assertEquals(unreadByRows.get(6), unreadByRows.get(4),
                "what is left unread does not follow the rows of the table");
        assertTrue(unreadByRows.get(4).stream().anyMatch(each -> each.startsWith("w.xs ")),
                "the count over the closure is said to be unread: " + unreadByRows.get(4));
    }
}
