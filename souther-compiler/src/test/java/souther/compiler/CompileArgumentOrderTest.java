package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The standard library takes its function first and its collection last (F#/Elm order), so calling a
 * combinator with the arguments the other way round is the mistake a newcomer makes first. The lambda
 * then sits on a parameter that takes a value, and the error must say so — which argument it landed
 * on, which argument takes the function, and the order to write — rather than reporting the block as
 * a value that escaped, a rule the caller has not met yet.
 */
class CompileArgumentOrderTest {

    private static final String MODULE = """
            module demo

            data Item = { name: String, price: Int }
            data Cart = { items: List<Item> }
            data Out = { n: Int }

            behavior tally : (c: Cart) -> Out
                constructs Out

            let tally (c) = Out { n = %s }
            """;

    private static CompileException rejects(String expr) {
        return assertThrows(CompileException.class, () -> Compiler.compile(MODULE.formatted(expr)));
    }

    @Test
    void aLambdaOnAValueParameterNamesTheParameterItLandedOn() {
        CompileException e = rejects("List.sum(List.map(c.items, (i) -> i.price))");

        String message = e.getMessage();
        assertTrue(message.contains("List.map"), message);
        assertTrue(message.contains("argument 2"), message);   // where the lambda was written
        assertTrue(message.contains("xs"), message);           // the parameter that takes a value
        assertFalse(message.contains("not a value"), message);
    }

    @Test
    void itPointsAtTheParameterThatTakesTheFunction() {
        CompileException e = rejects("List.sum(List.map(c.items, (i) -> i.price))");

        String message = e.getMessage();
        assertTrue(message.contains("argument 1"), message);   // where the function belongs
        assertTrue(message.contains("`f`"), message);
        assertTrue(message.contains("List.map(f, xs)"), message);
    }

    @Test
    void aFieldGetterIsReportedTheSameWay() {
        CompileException e = rejects("List.sum(List.map(c.items, .price))");

        String message = e.getMessage();
        assertTrue(message.contains("List.map(f, xs)"), message);
        assertFalse(message.contains("not a value"), message);
    }

    /** `List.fold` is sugar for `List.foldFrom(step, seed, xs, 0)`, so the report must keep the name
     * and the argument positions the caller wrote, not the ones the sugar expands to. */
    @Test
    void theFoldSugarIsReportedUnderTheNameThatWasWritten() {
        CompileException e = rejects("List.fold(0, (acc, x) -> acc + x.price, c.items)");

        String message = e.getMessage();
        assertTrue(message.contains("List.fold(step, seed, xs)"), message);
        assertFalse(message.contains("foldFrom"), message);
        assertFalse(message.contains("not a value"), message);
    }

    /** The same mistake made with a named helper instead of a lambda: the value lands on the function
     * parameter, and the report names the call as it was written (`List.map`, not the prelude
     * definition's bare `map`) and the order it takes. */
    @Test
    void aValueOnTheFunctionParameterNamesTheOrderToo() {
        String module = """
                module demo

                data Item = { name: String, price: Int }
                data Cart = { items: List<Item> }
                data Out = { n: Int }

                let priceOf (i: Item) : Int = i.price

                behavior tally : (c: Cart) -> Out
                    constructs Out

                let tally (c) = Out { n = List.sum(List.map(c.items, priceOf)) }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(module));

        String message = e.getMessage();
        assertTrue(message.contains("List.map(f, xs)"), message);
        assertFalse(message.contains("`let map`"), message);
    }

    @Test
    void theDeclaredOrderStillCompiles() {
        Compiler.compile(MODULE.formatted("List.fold((acc, x) -> acc + x.price, 0, c.items)"));
        Compiler.compile(MODULE.formatted("List.sum(List.map(.price, c.items))"));
    }
}
