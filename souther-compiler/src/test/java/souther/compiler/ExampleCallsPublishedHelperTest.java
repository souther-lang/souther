package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A row may apply a helper another module publishes (ADR-0075, ADR-0077). The reading module emits the
 * method, as it already does for a recursive helper it reaches: the declaring module's {@code $Fns} is
 * package-private and carries no method for a helper only its reader's example applies.
 */
class ExampleCallsPublishedHelperTest {

    private static final String PRICING = """
            module pricing exposing ( Amount, taxed, tiered )
            data Amount = Int

            let rate = 11

            let taxed (a: Amount) = Amount(a.value * rate / 10)

            partial let steps (n: Int) : Int = if n <= 0 then 0 else n + steps(n - 1)

            let tiered (n: Int) = Amount(steps(n))
            """;

    private static final String ORDER = """
            module order
            import pricing ( Amount, taxed )
            data Receipt = { total: Amount }
            behavior bill : (a: Amount) -> Receipt
                constructs Receipt
            let bill (a) = Receipt { total = a }
            example bill
              | (taxed(Amount(100))) -> Receipt { total = Amount(110) }
            """;

    @Test
    void aRowAppliesAPublishedHelper() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(PRICING, ORDER)));
    }

    @Test
    void aRowApplyingAPublishedHelperStillCatchesAMismatch() {
        String bad = ORDER.replace("-> Receipt { total = Amount(110) }", "-> Receipt { total = Amount(999) }");
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(PRICING, bad)));
        assertEquals("E1905", e.diagnostic().code());
    }

    @Test
    void aPublishedHelperCarriesWhatItReachesInItsOwnModule() {
        // `tiered` reaches `rate` (a value of pricing) and `steps` (a recursive helper of pricing,
        // which is not published). The reader applies `tiered` without importing either.
        String reader = """
                module order
                import pricing ( Amount, tiered )
                data Receipt = { total: Amount }
                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt
                let bill (a) = Receipt { total = a }
                example bill
                  | (tiered(4)) -> Receipt { total = Amount(10) }
                """;
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(PRICING, reader)));
    }
}
