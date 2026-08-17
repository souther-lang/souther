package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.msg.ExampleMessage;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An attached file's values are named by the rows written beside them, and not by the model.
 *
 * <p>An {@code examples for} file holds the rows, the fakes they run against, and the values those
 * rows name (spec §example-placement). Its values join the module its rows join, so from resolution
 * onwards they are reachable under the same names as the module's own — and the direction that may
 * be reached in is one way. A model that named one would not compile without a file of fixtures,
 * and a clause that named one would travel to an importer spelling a name the jar has no source
 * for: what is published is the module's own source, and an attached file adds nothing to it.
 *
 * <p>The refusal is written where a name is answered rather than as a walk over the declarations
 * that can write one, so the positions below are what one rule already covers rather than five
 * rules. What it does not cover is the {@code exposing} list, which is a list of names and not an
 * expression; that is held to the same rule where the list is read, and has its own case here.
 */
class AnAttachedFilesValuesAreForItsRowsTest {

    private static final String COMPANION = """
            examples for beside.rows

            let floor = 0

            example echo
                | "unchanged" : (Amount { n = 1 }) -> Amount { n = 1 }
            """;

    private static CompileException refused(String model) {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(model, COMPANION)));
        assertEquals("E1626", e.diagnostic().code());
        assertInstanceOf(ExampleMessage.TheModelNamesAValueAnAttachedFileDeclares.class,
                e.diagnostic().said());
        return e;
    }

    @Test
    void anInvariantMayNotNameOne() {
        refused("""
                module beside.rows exposing ( Amount, echo )

                data Amount = { n: Int }
                    invariant n >= floor

                behavior echo : (x: Amount) -> Amount
                let echo (x) = x
                """);
    }

    @Test
    void anEnsuresMayNotNameOne() {
        refused("""
                module beside.rows exposing ( Amount, echo )

                data Amount = { n: Int }

                behavior echo : (x: Amount) -> Amount
                    ensures atLeastFloor = value.n >= floor && value.n == x.n
                let echo (x) = x
                """);
    }

    @Test
    void aBehaviorsBodyMayNotNameOne() {
        refused("""
                module beside.rows exposing ( Amount, echo )

                data Amount = { n: Int }

                behavior echo : (x: Amount) -> Amount
                let echo (x) = Amount { n = x.n + floor }
                """);
    }

    @Test
    void aHelpersBodyMayNotNameOne() {
        refused("""
                module beside.rows exposing ( Amount, echo )

                data Amount = { n: Int }

                let bumped (n: Int) = n + floor

                behavior echo : (x: Amount) -> Amount
                let echo (x) = Amount { n = bumped(x.n) }
                """);
    }

    /** The one position the rule is stated a second time for, because a name in an `exposing` list
     *  is not answered where a name written in an expression is. */
    @Test
    void theExposingListMayNotNameOne() {
        refused("""
                module beside.rows exposing ( Amount, echo, floor )

                data Amount = { n: Int }

                behavior echo : (x: Amount) -> Amount
                let echo (x) = x
                """);
    }

    /** What the file is for. */
    @Test
    void aRowBesideItNamesOne() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module beside.rows exposing ( Amount, echo )

                data Amount = { n: Int }

                behavior echo : (x: Amount) -> Amount
                let echo (x) = x
                """, """
                examples for beside.rows

                let one = Amount { n = 1 }

                example echo
                    | "named" : (one) -> one
                """)));
    }

    /**
     * A row written inline in the model source names one too.
     *
     * <p>What decides this is the row and not which file it is written in: the values join the
     * module the rows join, and a row is a row wherever it stands. Answered by the file instead, the
     * same row would be admitted beside the attached values and refused beside the behavior it is
     * about.
     */
    @Test
    void aRowInTheModelSourceNamesOne() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module beside.rows exposing ( Amount, echo )

                data Amount = { n: Int }

                behavior echo : (x: Amount) -> Amount
                let echo (x) = x

                example echo
                    | "named" : (one) -> one
                """, """
                examples for beside.rows

                let one = Amount { n = 1 }
                """)));
    }

    /** A fake is what the rows run against, so it names one as a row does. */
    @Test
    void aFakeNamesOne() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module beside.rows exposing ( Amount, echo )

                data Amount = { n: Int }

                behavior lookup : (x: Amount) -> Amount

                behavior echo : (x: Amount) -> Amount
                    depends on lookup
                let echo (x, lookup) = lookup(x)
                """, """
                examples for beside.rows

                let one = Amount { n = 1 }

                fake lookup
                    | (one) -> one

                example echo
                    | "named" : (one) -> one
                """)));
    }

    /** One attached value names another: both are the rows', and neither is the model. */
    @Test
    void oneAttachedValueNamesAnother() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module beside.rows exposing ( Amount, echo )

                data Amount = { n: Int }

                behavior echo : (x: Amount) -> Amount
                let echo (x) = x
                """, """
                examples for beside.rows

                let base = 1
                let one = Amount { n = base }

                example echo
                    | "named" : (one) -> one
                """)));
    }

    /** The other direction is not the one refused: an attached value naming a model helper is a
     *  fixture reading the model, which is what a fixture is for. */
    @Test
    void anAttachedValueNamesAModelHelper() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module beside.rows exposing ( Amount, echo )

                data Amount = { n: Int }

                let base = 1

                behavior echo : (x: Amount) -> Amount
                let echo (x) = x
                """, """
                examples for beside.rows

                let one = Amount { n = base }

                example echo
                    | "named" : (one) -> one
                """)));
    }

    /** A module with no attached file has no value this rule is about, and a `let` of its own that
     *  every other one names is reached as freely as it was. */
    @Test
    void aModulesOwnValueIsNamedByItsOwnDeclarations() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module beside.rows exposing ( Amount, echo )

                let floor = 0

                data Amount = { n: Int }
                    invariant n >= floor

                behavior echo : (x: Amount) -> Amount
                let echo (x) = x
                """));
    }
}
