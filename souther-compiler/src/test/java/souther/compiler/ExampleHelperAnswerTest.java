package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A row whose whole expectation is a helper's answer asserts the value that helper answered with.
 *
 * <p>A fixture is built in the neutral form a decoder reads, because what encloses it is built the one
 * way. Nothing encloses the expectation, and a helper has already built its value — so reading it back
 * into the neutral form left the comparison holding a form against a value. It showed wherever the output
 * type has a case: a newtype was compared against its inner value, a record against its field map, a case
 * of a union against its field map and tag. A collection and a primitive held, because there the declared
 * output type is enough to read the form back with (issue #214).
 */
class ExampleHelperAnswerTest {

    private static final String RECORD = """
            module demo

            data In  = { n: Int }
            data Out = { m: Int }

            behavior run : (i: In) -> Out
                constructs Out

            let run (i) = doubled(i.n)

            let doubled (n: Int) = Out { m = n * 2 }
            """;

    private static Diagnostic only(String model) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(model));
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        return e.diagnostics().get(0);
    }

    @Test
    void aRecordAHelperAnsweredWith() {
        assertDoesNotThrow(() -> Compiler.compile(RECORD + """

                example run
                    | "the rule the row is about" : (In { n = 5 }) -> doubled(5)
                """));
    }

    @Test
    void aNewtypeAHelperAnsweredWith() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Amount = Int
                data In     = { n: Int }

                behavior run : (i: In) -> Amount

                let run (i) = taxed(i.n)

                let taxed (n: Int) = Amount(n * 110 / 100)

                example run
                    | "a newtype" : (In { n = 100 }) -> taxed(100)
                """));
    }

    @Test
    void aCaseOfAUnionAHelperAnsweredWith() {
        // The case is in the value the helper answered with; nothing in the text says it.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Yes     = { m: Int }
                data No      = { why: String }
                data Verdict = Yes | No
                data In      = { n: Int }

                behavior run : (i: In) -> Verdict
                    constructs Yes

                let run (i) = judged(i.n)

                let judged (n: Int) = Yes { m = n * 2 }

                example run
                    | "a case of a union" : (In { n = 5 }) -> judged(5)
                """));
    }

    @Test
    void aDateAHelperAnsweredWith() {
        // A `Date`'s neutral form is the parsed temporal while its encoder writes ISO text, so the two
        // sides of this row were built and shown in different notations.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Out = { on: Date }
                data In  = { n: Int }

                behavior run : (i: In) -> Out
                    constructs Out

                let run (i) = dated(i.n)

                let dated (n: Int) = Out { on = Date("2026-07-30") }

                example run
                    | "a date-bearing record" : (In { n = 5 }) -> dated(5)
                """));
    }

    @Test
    void aNameForAHelpersAnswer() {
        // The name stands for the answer, so the row asserts what the helper answered with. This was
        // refused as an arm the target cannot produce, because a helper's case is not in the text.
        assertDoesNotThrow(() -> Compiler.compile(RECORD + """

                let expected = doubled(5)

                example run
                    | "a name for the answer" : (In { n = 5 }) -> expected
                """));
    }

    @Test
    void aCollectionAHelperAnsweredWith() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data In  = { n: Int }
                data Out = { m: Int }

                behavior lines : (i: In) -> List<Out>
                    constructs Out

                let lines (i) = listed(i.n)

                let listed (n: Int) = [ Out { m = n }, Out { m = n } ]

                example lines
                    | "a list of records" : (In { n = 5 }) -> listed(5)
                """));
    }

    @Test
    void aHelpersAnswerStillHasToHold() {
        Diagnostic d = only(RECORD + """

                example run
                    | "the wrong answer" : (In { n = 5 }) -> doubled(6)
                """);

        assertEquals("E1905", d.code());
        assertEquals("Out { m = 12 }", d.diff().expectedType(),
                "the expectation is the value the helper answered with");
        assertEquals("Out { m = 10 }", d.diff().actualType(),
                "and both sides are shown in one notation");
    }

    @Test
    void aNamedHelperAnswerStillHasToHold() {
        Diagnostic d = only(RECORD + """

                let expected = doubled(6)

                example run
                    | "the wrong answer, named" : (In { n = 5 }) -> expected
                """);

        assertEquals("E1905", d.code());
        assertEquals("Out { m = 12 }", d.diff().expectedType());
    }

    @Test
    void aHelperAnsweringACaseTheTargetCannotProduceIsAMismatch() {
        // Which case a helper answers with is not known before it runs, so this is not an arm error: the
        // row is compared, and it does not hold.
        Diagnostic d = only("""
                module demo

                data Yes     = { m: Int }
                data No      = { why: String }
                data Verdict = Yes | No
                data Other   = { m: Int }
                data In      = { n: Int }

                behavior run : (i: In) -> Verdict
                    constructs Yes

                let run (i) = judged(i.n)

                let judged (n: Int) = Yes { m = n * 2 }

                let elsewhere (n: Int) = Other { m = n * 2 }

                example run
                    | "a case the target cannot produce" : (In { n = 5 }) -> elsewhere(5)
                """);

        assertEquals("E1905", d.code());
    }

    @Test
    void aHelperInsideTheExpectationIsUnchanged() {
        // The neutral form is for what encloses a fixture, and a record encloses this one.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Amount = Int
                data In     = { n: Int }
                data Out    = { total: Amount }

                behavior run : (i: In) -> Out
                    constructs Out
                    constructs Amount

                let run (i) = Out { total = taxed(i.n) }

                let taxed (n: Int) = Amount(n * 110 / 100)

                example run
                    | "a helper inside a record" : (In { n = 100 }) -> Out { total = taxed(100) }
                """));
    }
}
