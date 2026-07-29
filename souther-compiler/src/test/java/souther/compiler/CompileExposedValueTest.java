package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module publishes its values. A value is part of what a module offers — a limit a rule is written
 * against, the representative record an example is stated with — and a reader of that module had to
 * write it out again, which is what left an import list naming ten types for one fixture (issue
 * #163).
 *
 * <p>What is published is decided by the type, not by the shape of the definition: a value holding a
 * function is not published, and neither is a helper, because neither crosses into another module as
 * a value. A published value's own type must be published; the types its body happens to use are its
 * own business.
 */
class CompileExposedValueTest {

    private static final String UPSTREAM = """
            module pricing exposing ( Amount, Priced, cap, standard )

            data Amount = Int
            data Priced = { total: Amount, note: String }

            let cap = Amount(1000)
            let standard = Priced { total = cap, note = "standard" }
            """;

    @Test
    void aValueIsPublishedAndReadInAnotherModule() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UPSTREAM, """
                module order exposing ( Receipt, bill )

                import pricing ( Amount, Priced, cap )

                data Receipt = { total: Amount }

                behavior bill : (p: Priced) -> Receipt constructs Receipt, Amount
                let bill (p) = Receipt { total = Amount(p.total.value + cap.value) }
                """)));
    }

    /** The point of publishing a value: a row names it instead of restating the record, and the
     * importing module names one type rather than every type inside it. */
    @Test
    void anExampleRowNamesAnImportedValue() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UPSTREAM, """
                module order exposing ( Receipt, bill )

                import pricing ( Priced, standard )

                data Receipt = { note: String }

                behavior bill : (p: Priced) -> Receipt constructs Receipt
                let bill (p) = Receipt { note = p.note }

                example bill
                    | "the standard price is billed by its note" : (standard)
                        -> Receipt { note = "standard" }
                """)));
    }

    @Test
    void anImportedValueMayBeSpread() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UPSTREAM, """
                module order exposing ( bill )

                import pricing ( Amount, Priced, standard )

                behavior bill : (p: Priced) -> Priced constructs Priced, Amount
                let bill (p) = Priced { ...standard, note = "billed" }
                """)));
    }

    @Test
    void aPublishedValueMustHaveAPublishedType() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( cap )

                data Amount = Int

                let cap = Amount(1000)
                """));

        assertTrue(e.getMessage().contains("Amount"), e.getMessage());
    }

    /** Only the value's own type crosses. What its body reached for on the way is not the reader's
     * concern, and requiring it would put every inner type back in the import list. */
    @Test
    void aTypeUsedOnlyInsideAPublishedValuesBodyStaysUnpublished() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module pricing exposing ( Amount, cap )

                data Amount = Int
                data Step = Int

                let base = Step(10)
                let cap = Amount(base.value * 100)
                """));
    }

    @Test
    void aValueHoldingAFunctionIsNotPublished() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( raise )

                data Amount = Int

                let raise = (a) -> a + 1
                """));

        assertTrue(e.getMessage().contains("raise"), e.getMessage());
    }

    @Test
    void aHelperIsStillNotPublished() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( Amount, twice )

                data Amount = Int

                let twice (a: Int) = a * 2
                """));

        assertTrue(e.getMessage().contains("twice"), e.getMessage());
    }

    /** A value crosses a project boundary too: what is published is the declaration, read back from
     * the jar, and a value is substituted from that like any other. */
    @Test
    void aValueCrossesAProjectBoundary() throws Exception {
        Map<String, byte[]> classes = Compiler.compile(UPSTREAM);
        ModulePath path = classes::get;

        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module app.billing exposing ( Receipt, bill )

                import pricing ( Amount, Priced, cap )

                data Receipt = { total: Amount }

                behavior bill : (p: Priced) -> Receipt constructs Receipt, Amount
                let bill (p) = Receipt { total = Amount(p.total.value + cap.value) }
                """), path));
    }

    /** A value another module keeps to itself has no name here, as any unexposed name has. */
    @Test
    void anUnpublishedValueCannotBeImported() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module pricing exposing ( Amount )

                        data Amount = Int

                        let cap = Amount(1000)
                        """, """
                        module order exposing ( bill )

                        import pricing ( Amount, cap )

                        behavior bill : (a: Amount) -> Amount constructs Amount
                        let bill (a) = Amount(a.value + cap.value)
                        """)));

        assertTrue(e.getMessage().contains("cap"), e.getMessage());
    }
}
