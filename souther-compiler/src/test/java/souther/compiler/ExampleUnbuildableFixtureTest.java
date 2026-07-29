package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fixture that cannot be built is reported as one, in every position a fixture is written. The
 * expected side used to be compared against a value nothing had built, so a correct row was reported
 * as a mismatch against an empty expected value; a {@code with} value that could not be built was
 * reported as a dependency with no fake at all, which the row plainly gives.
 */
class ExampleUnbuildableFixtureTest {

    private static final String BASE = """
            module demo

            data Amount = Int

            data Receipt = { total: Amount }

            behavior bill : (a: Amount) -> Receipt
                constructs Receipt

            let bill (a) = Receipt { total = a }
            """;

    private static final String INJECTED = """
            module demo

            data Amount = Int

            data Receipt = { total: Amount }

            behavior quote : (a: Amount) -> Amount

            behavior bill : (a: Amount) -> Receipt
                depends on quote
                constructs Receipt

            let bill (a, quote) = Receipt { total = quote(a) }
            """;

    private static Diagnostic only(String model) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(model));
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        return e.diagnostics().get(0);
    }

    @Test
    void anExpectedValueThatCannotBeBuiltIsNotReportedAsAMismatch() {
        // `Amount` is a newtype over Int, so `Amount("x")` cannot be built. The row asserts nothing
        // about a mismatch — there is no expected value to compare against.
        Diagnostic d = only(BASE + """
                example bill
                  | (Amount(1)) -> Receipt { total = Amount("x") }
                """);

        assertEquals("E1903", d.code(), "an expected value that cannot be built is a fixture error");
        assertEquals("check.example.expected", d.messageKey());
        assertEquals(null, d.diff(), "there is no value to show against the behavior's result");
    }

    @Test
    void aWithValueThatCannotBeBuiltIsNotReportedAsAMissingFake() {
        Diagnostic d = only(INJECTED + """
                example bill
                  | (Amount(1)) with quote = Amount("x") -> Receipt { total = Amount(1) }
                """);

        assertEquals("E1908", d.code());
        assertEquals("check.fake.value", d.messageKey(),
                "the row supplies a fake; what failed is building its value");
    }

    @Test
    void aDependencyWithNoFakeStillReportsThatNoFakeWasSupplied() {
        Diagnostic d = only(INJECTED + """
                example bill
                  | (Amount(1)) -> Receipt { total = Amount(1) }
                """);

        assertEquals("E1908", d.code());
        assertEquals("check.fake.missing", d.messageKey());
    }

    @Test
    void aRowThatDoesNotHoldIsStillAMismatch() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(BASE + """
                example bill
                  | (Amount(1)) -> Receipt { total = Amount(2) }
                """));

        assertTrue(e.getMessage().contains("E1905"), e.getMessage());
    }
}
