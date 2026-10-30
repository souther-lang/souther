package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a way states of one place of a record says something of another place of it only where a
 * rule of the declarations reads the two together. A guard on {@code a.days} leaves
 * {@code a.amount} the values it took before, though a rule reads {@code amount} alone.
 */
class AStatementOnAPlaceNoRuleReadsWithATermLeavesTheTermItsReachTest {

    private static final String PAY = """
            data Pay = { days: Int, amount: Int }
                invariant amount >= 0
            """;

    private static final String PREAMBLE = """
            module demo

            %s
            data Ok
            data No
            data Row = { grade: Int, lowerBound: Int }
            let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                     Row { grade = 2, lowerBound = 100 },
                                     Row { grade = 3, lowerBound = 300 } ]
            let gradeRowFor (m: Int): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { grade = 0, lowerBound = 0 }, table)

            behavior f : (a: Pay, b: Pay, c: Pay) -> Ok | No
            let f (a, b, c) = {
                %s
                Ok
            }
            """;

    private static final String KEPT = "List.filter(r -> r.days >= 17, [a, b, c])";

    /** The places the report says nothing is read of. */
    private static List<String> unread(String data, String body) {
        Compilation compilation = Compilation.ofSource(PREAMBLE.formatted(data, body), "Main");
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

    /** A guard on the days of one record and a sum of the amounts of two: a rule reads the amount
     *  alone, so the days say nothing of it. */
    @Test
    void aGuardOnAnotherPlaceOfARecordLeavesTheSumAsItWas() {
        assertEquals(List.of(),
                unread(PAY, "guard a.days >= 17 && a.amount + b.amount >= 100 else No"));
    }

    /** The control: the same guard on the days of another record. */
    @Test
    void aGuardOnAnotherRecordLeavesTheSumAsItWas() {
        assertEquals(List.of(),
                unread(PAY, "guard c.days >= 17 && a.amount + b.amount >= 100 else No"));
    }

    /** Which months are kept is stated of each month's days, and the total is of their amounts. */
    @Test
    void aTotalOverTheMonthsKeptIsRead() {
        assertEquals(List.of(), unread(PAY, "let p = " + KEPT
                + "\n    guard List.sum(List.map(r -> r.amount, p)) >= 100 else No"));
    }

    /** The shape of a grade looked up for the average of the months kept. */
    @Test
    void anAverageOverTheMonthsKeptHeldAgainstATableIsRead() {
        assertEquals(List.of(), unread(PAY, "let p = " + KEPT + """

                guard List.length(p) >= 1 else No
                guard gradeRowFor(Rational.toInt(DOWN, List.sum(List.map(r -> r.amount, p))
                                                       / List.length(p))).grade >= 2 else No"""));
    }

    /** Each term takes its own amount only where its own days allow. */
    @Test
    void aTermTakenOnlyWhereItsOwnDaysAllowAreRead() {
        assertEquals(List.of(), unread(PAY, """
                guard (if a.days >= 17 then a.amount else 0)
                    + (if b.days >= 17 then b.amount else 0) >= 100 else No"""));
    }

    /** A rule that holds the amount to the days moves it with them, and the guard on the days
     *  says something of it again: what it did not show before it still does not. */
    @Test
    void aRuleHoldingTheAmountToTheDaysKeepsTheGuardOnThem() {
        List<String> unread = unread("""
                data Pay = { days: Int, amount: Int }
                    invariant amount >= 0
                    invariant amount >= days
                """, "guard a.days >= 17 && a.amount + b.amount >= 100 else No");
        assertTrue(unread.contains("b.amount"), unread.toString());
    }

    /** The rule need not read the two together itself: it holds the amount to a third place that
     *  another holds to the days. */
    @Test
    void aRuleThroughAThirdPlaceKeepsTheGuardOnTheDays() {
        List<String> unread = unread("""
                data Pay = { days: Int, extra: Int, amount: Int }
                    invariant amount >= extra
                    invariant extra >= days
                """, "guard a.days >= 17 && a.amount + b.amount >= 100 else No");
        assertTrue(unread.contains("b.amount"), unread.toString());
    }
}
