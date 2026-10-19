package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total over what the body maps a list of the input to, which is no number of the input, says
 * what stopped the value each element comes to where the arithmetic stopped on it — and says what
 * it said before where it did not.
 */
class ATotalOverTheInputsRunSaysWhatStoppedItsElementTest {

    private static final String MODEL = """
            module p
            data Ln = { a: Decimal, b: Decimal, q: Decimal, price: Decimal }
            data Ok
            data No
            behavior f : (ls: List<Ln>) -> Ok | No
            let f (ls) = {
                guard Decimal.compare(List.sum(%s), List.sum(List.map(r -> r.b, ls)) * 0.6m) >= 0
                    else No
                Ok
            }
            """;

    private static final String OF_THE_WHOLE_ANSWER = "number_of_what_an_operation_answers";

    private static String json(String total) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(total), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).json(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void anElementThatIsALinearFormIsRead() {
        String report = json("List.map(r -> r.a, ls)");
        assertFalse(report.contains(OF_THE_WHOLE_ANSWER), report);
        assertFalse(report.contains("no_form_of_what_it_answers"), report);
        assertFalse(report.contains("outside_the_linear_fragment"), report);
    }

    @Test
    void aRoundedElementIsSaidToHaveNoForm() {
        String report = json("List.map(r -> Decimal.round(2, HALF_UP, r.a), ls)");
        assertTrue(report.contains("no_form_of_what_it_answers"), report);
        assertFalse(report.contains(OF_THE_WHOLE_ANSWER), report);
    }

    @Test
    void aProductOfTwoValuesIsSaidToBeOutsideTheLinearFragment() {
        String report = json("List.map(r -> r.q * r.price, ls)");
        assertTrue(report.contains("outside_the_linear_fragment"), report);
        assertFalse(report.contains(OF_THE_WHOLE_ANSWER), report);
    }

    /** The value each element comes to is linear, so what stopped the total is not the value. */
    @Test
    void anElementThatIsLinearIsNotSaidToBeAnythingElseWhenTheTotalStops() {
        String report = json("List.map(r -> r.a, List.filter(r -> r.q > 0.0m, ls))");
        assertFalse(report.contains("outside_the_linear_fragment"), report);
        assertFalse(report.contains("no_form_of_what_it_answers"), report);
    }
}
