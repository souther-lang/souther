package souther.compiler.report;

import java.util.List;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total over the cases of a sum is read as the amount one element answers only where a list of
 * one element is a row, and every case can stand at every amount the others can.
 *
 * <p>The control is the model of {@link ATotalOverTheCasesOfASumIsReadWhereTheCaseAnswersAnAmountTest}:
 * both cases answer a {@code Yen}, the list may hold one, and the numbers of the input are read as
 * related to the total. Each test changes one thing that takes a value the total would otherwise
 * be shown to reach, and that reading must go.
 */
class ATotalOverTheCasesOfASumIsNotReadWhereTheCasesCannotAnswerAnAmountTest {

    private static final String RELATES = "it relates the value here to another value rather than"
            + " dividing the values here, about `List.sum(";

    /**
     * The model, with the second case answering {@code agreedAmount}, declared by
     * {@code extraType}, and a list of deductions held to {@code listInvariant}.
     */
    private static String model(String agreedAmount, String extraType, String listInvariant) {
        return """
                module probe.payslip

                data Yen = Int
                    invariant value >= 0

                %s

                data Statutory = { amount: Yen }
                data Agreed = { amount: %s, code: Int }
                data Deduction = Statutory | Agreed

                data Deductions = List<Deduction>
                    invariant %s

                data Ok
                data Short

                let amountOf (d: Deduction): Int =
                    match d with
                        | Statutory { amount } -> amount.value
                        | Agreed { amount } -> amount.value

                let total (ds: Deductions): Int =
                    List.sum(List.map(d -> amountOf(d), ds.value))

                behavior pay : (limit: Int, deductions: Deductions) -> Ok | Short
                let pay (limit, deductions) = {
                    guard limit >= total(deductions) else Short
                    Ok
                }
                """.formatted(extraType, agreedAmount, listInvariant);
    }

    private static final String ANY_LIST = "List.length(value) >= 0";

    private static final String NEVER = """
            data Never = Int
                invariant value >= 10 && value < 5""";

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals("[]", compilation.errors().toString(), source);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** The model as the other test has it, which the changes below are measured against. */
    @Test
    void theControlIsRead() {
        String report = report(model("Yen", "", ANY_LIST));

        assertTrue(report.contains(RELATES), report);
    }

    /**
     * One case no value can be written for. The declarations refuse it before any rule is read
     * for a total, so no run of it is ever offered as one.
     */
    @Test
    void aCaseNoValueCanBeWrittenForIsRefusedBeforeItIsRead() {
        Compilation compilation = Compilation.ofSource(model("Never", NEVER, ANY_LIST), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of("E1013"), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList());
    }

    /** A list that can only be empty has no element to answer an amount, and the total is nought. */
    @Test
    void aListThatCanOnlyBeEmptyIsNoRunOfAnAmount() {
        String report = report(model("Yen", "", "List.length(value) <= 0"));

        assertFalse(report.contains(RELATES), report);
    }
}
