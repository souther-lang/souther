package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One name in the value namespace means one thing. A data reaches that namespace — a unit data is a
 * value, a newtype is applied to what it wraps, a record is constructed by its name — so a
 * {@code let} of that name would be a second answer to the same spelling, and the type won because
 * names resolve to types first.
 *
 * <p>Elm keeps the two apart by capitalization and F# lets the later binding shadow the earlier one.
 * Souther writes Japanese identifiers and does not read case, so neither device is available and the
 * collision is refused where it is declared.
 *
 * <p>A behavior and a {@code let} of one name are not a collision: they are the declaration and the
 * implementation of one thing.
 */
class CompileValueNamespaceCollisionTest {

    private static CompileException refused(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source));
    }

    @Test
    void aValueMayNotBeNamedLikeAUnitData() {
        CompileException e = refused("""
                module demo

                data Ready
                data In = { n: Int }

                let Ready = In { n = 1 }

                behavior go : (i: In) -> Ready
                let go (i) = Ready
                """);

        assertTrue(e.getMessage().contains("Ready"), e.getMessage());
    }

    @Test
    void aHelperMayNotBeNamedLikeANewtype() {
        CompileException e = refused("""
                module demo

                data Amount = Int
                data In = { n: Int }

                let Amount (n) = n + 1

                behavior go : (i: In) -> In
                let go (i) = In { n = Amount(i.n) }
                """);

        assertTrue(e.getMessage().contains("Amount"), e.getMessage());
    }

    @Test
    void aValueMayNotBeNamedLikeARecord() {
        CompileException e = refused("""
                module demo

                data In = { n: Int }

                let In = 1

                behavior go : (i: In) -> In
                let go (i) = i
                """);

        assertTrue(e.getMessage().contains("In"), e.getMessage());
    }

    /** {@code None} is the language's own name for the empty optional, so a module cannot take it. */
    @Test
    void aValueMayNotBeNamedLikeABuiltin() {
        CompileException e = refused("""
                module demo

                data In = { n: Int }

                let None = 1

                behavior go : (i: In) -> In
                let go (i) = In { n = i.n + None }
                """);

        assertTrue(e.getMessage().contains("None"), e.getMessage());
    }

    @Test
    void aBehaviorAndItsImplementationShareOneName() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { n = i.n }
                """));
    }

    /** A behavior taking nothing is implemented by a value: the parameter counts agree, which is all
     * the pairing asks. */
    @Test
    void aValueImplementsABehaviorThatTakesNothing() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Stamp = { at: String }

                behavior origin : () -> Stamp constructs Stamp
                let origin = Stamp { at = "1970-01-01" }
                """));
    }

    private static final String PUBLISHES_TAG = """
            module lib
            exposing ( Tag )

            let Tag (n: Int) = n + 1
            """;

    /**
     * A definition another module publishes is written here bare, so it lands in this namespace
     * exactly where a data of that name already is. Reached through an import it used to walk past
     * the check: bare `Tag` was the unit data and `Tag(i.n)` the imported helper, in one body.
     */
    @Test
    void anImportedHelperMayNotBeNamedLikeALocalData() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(java.util.List.of(PUBLISHES_TAG, """
                        module app
                        exposing ( Out, In, go )

                        import lib ( Tag )

                        data Tag
                        data In = { n: Int }
                        data Out = { bumped: Int }

                        behavior go : (i: In) -> Out | Tag
                            constructs Out
                        let go (i) = {
                            guard i.n > 0
                                else Tag
                            Out { bumped = Tag(i.n) }
                        }
                        """)));

        assertTrue(e.getMessage().contains("Tag"), e.getMessage());
    }

    /** The qualifier is the only spelling that reaches the library, so a data of that name hides it. */
    @Test
    void aDataMayNotBeNamedLikeAStandardLibraryQualifier() {
        CompileException e = refused("""
                module demo

                data List = String
                data In = { s: String }
                data Out = { n: Int }

                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { n = String.length(i.s) }
                """);

        assertTrue(e.getMessage().contains("List"), e.getMessage());
    }
}
