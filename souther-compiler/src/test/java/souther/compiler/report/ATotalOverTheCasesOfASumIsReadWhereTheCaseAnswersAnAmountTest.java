package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total over a list whose elements are a sum of records, compared with a total of two numbers
 * of the input.
 *
 * <p>Each element answers the amount of the case it is, and the amount is a newtype read as
 * {@code .value} after the {@code match}. The total is what each element's case comes to, so the
 * comparison is a relation of the two numbers and that total, and the line it draws is where the
 * gross equals the total.
 *
 * <p>Three things had to be true for it to be read. The value of a newtype standing on a
 * {@code match} is the value of each arm; one element standing alone comes to the amount of
 * whichever case it is; and a value of the sum is shown to exist where a case of it holds one.
 */
class ATotalOverTheCasesOfASumIsReadWhereTheCaseAnswersAnAmountTest {

    private static final String MODEL = """
            module probe.payslip

            data Yen = Int
                invariant value >= 0

            data Statutory = { amount: Yen }
            data Agreed = { amount: Yen, code: Int }
            data Deduction = Statutory | Agreed

            data Earnings = { fixed: Yen, uplift: Yen }

            data Ok
            data Short

            let amountOf (d: Deduction): Yen =
                match d with
                    | Statutory { amount } -> amount
                    | Agreed { amount } -> amount

            let sumOf (ds: List<Deduction>): Int =
                List.sum(List.map(d -> amountOf(d).value, ds))

            let total (ds: List<Deduction>): Yen = Yen(sumOf(ds))

            let grossOf (e: Earnings): Yen = e.fixed + e.uplift

            behavior pay : (earnings: Earnings, deductions: List<Deduction>) -> Ok | Short
                constructs Yen
            let pay (earnings, deductions) = {
                guard grossOf(earnings) >= total(deductions) else Short
                Ok
            }

            example pay
                | "enough" : (Earnings { fixed = Yen(100), uplift = Yen(0) }, [Statutory { amount = Yen(60) }, Agreed { amount = Yen(40), code = 1 }]) -> Ok
                | "short" : (Earnings { fixed = Yen(99), uplift = Yen(0) }, [Statutory { amount = Yen(60) }, Agreed { amount = Yen(40), code = 1 }]) -> Short
            """;

    private static String report() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** The rule is read: no part of it is left unread, and the rows are at its line. */
    @Test
    void theRuleIsReadAndTheRowsAreAtItsLine() {
        String report = report();

        assertFalse(report.contains("a part of what it states was not read"), report);
        assertFalse(report.contains("written in a form this compiler does not read"), report);
        assertFalse(report.contains("no row is at the ON point"), report);
        assertFalse(report.contains("no row is at the OFF point"), report);
    }

    /** And the numbers of the input are read as relating to the total, and divided no way. */
    @Test
    void theNumbersOfTheInputAreReadAsRelatedToTheTotal() {
        String report = report();

        assertTrue(report.contains("it relates the value here to another value rather than"
                + " dividing the values here, about `earnings.fixed`"), report);
        assertTrue(report.contains("it relates the value here to another value rather than"
                + " dividing the values here, about `earnings.uplift`"), report);
    }
}
