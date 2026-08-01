package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An example's expected value is asserted by the language's equality, so a Decimal's scale is not
 * part of what the row states. What a row states is which value the input yields, and 1.0 and 1 are
 * one value.
 */
class ExampleDecimalMatchTest {

    private static final String MODULE = """
            module demo

            data Req = { rate: Decimal }
            data Out = { rates: List<Decimal>, total: Decimal }

            behavior go : (r: Req) -> Out
                constructs Out
            let go (r) = Out { rates = [r.rate], total = r.rate }

            example go
                | "the same amount at another scale" :
                    (Req { rate = 1m }) -> Out { rates = [1.00m], total = 1.00m }
            """;

    @Test
    void anExpectedAmountMatchesAtAnotherScale() {
        assertDoesNotThrow(() -> Compiler.compile(MODULE));
    }

    @Test
    void aDifferentAmountStillFails() {
        assertThrows(CompileException.class,
                () -> Compiler.compile(MODULE.replace("total = 1.00m", "total = 2m")));
    }

    private static final String FAKED = """
            module demo

            data Req = { rate: Decimal }
            data Out = { label: String }

            behavior bandOf : (rate: Decimal) -> String

            behavior go : (r: Req) -> Out
                constructs Out
                depends on bandOf
            let go (r, bandOf) = Out { label = bandOf(r.rate) }

            fake bandOf
                | (1.0m) -> "one"

            example go
                | "the same amount at another scale finds its row" :
                    (Req { rate = 1m }) -> Out { label = "one" }
            """;

    /** A fake's rows are matched by value equality (spec 22), which is the same equality everywhere
     *  else: an amount written at one scale is the amount a call arrives with at another. */
    @Test
    void aFakeRowMatchesTheSameAmountAtAnotherScale() {
        assertDoesNotThrow(() -> Compiler.compile(FAKED));
    }

    @Test
    void aFakeRowStillMissesADifferentAmount() {
        assertThrows(CompileException.class,
                () -> Compiler.compile(FAKED.replace("| (1.0m) ->", "| (2m) ->")));
    }
}
