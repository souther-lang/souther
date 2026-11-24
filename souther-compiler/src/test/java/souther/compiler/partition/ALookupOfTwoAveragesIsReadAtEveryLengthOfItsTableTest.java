package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence.NotRead;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A lookup of two averages is read at every length of its table or at none: whether a month is
 * left unread does not follow where the readings of one condition ran out.
 *
 * <p>The lookup compares each row with two averages of months two filters keep. The ways the two
 * filters keep their months multiply at every row, so at two rows the condition that compares a
 * row with an average runs out of the readings of one condition, and at one row it does not.
 * What a fork over it is left stating is not read off what was got to before that
 * ({@link WhatAForkTests.PartsRead}): the comparison that states it says what stopped it, and a
 * fork of the lookup states nothing more. One length at which the reading stops stands for them
 * all, because a reading that stopped hands the fork no parts and so nothing that turns on where
 * it stopped.
 *
 * <p>The second average is compared beside a count over a closure of its own: how many elements
 * of {@code w.xs} hold a list of distinct numbers. That count is a part of what the comparison
 * states that no reader of the values answers for.
 */
class ALookupOfTwoAveragesIsReadAtEveryLengthOfItsTableTest {

    private static final String SOURCE = """
            module demo

            data Yen = Int
                invariant value >= 0
            data Days = Int
            data Month = { days: Days, pay: Yen }
            data Window = { a1: Month, a2: Month, b1: Month, b2: Month, xs: List<List<Int>> }
            data Row = { grade: Int, lowerBound: Yen, upperBound: Yen }
            data Decision = { grade: Int }
            data NoPayable = { nothing: Int }
            let table: List<Row> = [
                Row { grade = 1, lowerBound = Yen(0), upperBound = Yen(999) },
                Row { grade = 2, lowerBound = Yen(1000), upperBound = Yen(1999) } ]
            let gradeRowFor (ma: Yen, mb: Yen, n: Int): Row =
                List.fold((acc, r) ->
                              if r.lowerBound <= ma && mb.value + n <= r.upperBound.value
                              then r else acc,
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
                Decision { grade = gradeRowFor(averageOf(pa), averageOf(pb),
                    List.length(List.filter(ys -> List.allDistinctBy(k -> k, ys), w.xs))).grade }
            }
            """;

    /** What the report leaves unread, read once for both tests. The row search is not asked: what
     *  is left unread does not turn on it. */
    private static final List<NotRead> UNREAD = unread();

    private static List<NotRead> unread() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main").allowing(
                Allowances.DECLARED.with(CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION, 32));
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        ACompiledModel.compiles(compilation);
        List<NotRead> out = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each :
                AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            out.addAll(each.partition().notRead());
        }
        return out;
    }

    /**
     * At a length where the comparison of a row with an average runs out of the readings of one
     * condition, nothing is left unread at that figure: the fork is offered no parts of a reading
     * that stopped, so it says nothing of where the reading stopped.
     */
    @Test
    void aLengthTheReadingRunsOutAtLeavesNothingUnreadAtTheFigure() {
        assertEquals(List.of(), said(UNREAD.stream().filter(one -> !one.figures().isEmpty())),
                "what is left unread at a figure where the reading runs out");
    }

    /**
     * And what the comparison states beside the average is not lost where the reading runs out:
     * the count over the closure is nothing a reader of the values answers for, so the report
     * says it was not read.
     */
    @Test
    void aPartOfTheComparisonNoReaderAnswersForIsSaidWhereTheReadingRunsOut() {
        assertTrue(UNREAD.stream().anyMatch(one -> one.at().equals("w.xs")),
                () -> "the count over the closure is said to be unread: " + said(UNREAD.stream()));
    }

    /** Each entry as its position, why and at which figure. */
    private static List<String> said(Stream<NotRead> entries) {
        return entries.map(one -> one.at() + " " + one.reason() + " " + one.figures()).toList();
    }
}
