package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An invariant names what is in scope where it is written, and a definition another module publishes
 * is in scope there like any other name. A limit several modules' types are written against is
 * written once, in the module that owns it.
 *
 * <p>What an invariant may name is what travels with it: a published value is substituted where it is
 * named and a published helper expanded where it is called, both closed by the module that declares
 * them, so the settled invariant names nothing of that module. A module reading the type from a jar
 * reads the invariant as written and resolves the name against the declaring module, which is why
 * that module is on its class path.
 */
class CompileInvariantImportedDefinitionTest {

    private static final String LIMITS = """
            module limits exposing ( maxLen, fits )

            let maxLen = 3

            let fits (s: String) : Bool = String.length(s) <= maxLen
            """;

    @Test
    void anInvariantNamesAnImportedValue() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(LIMITS, """
                module ids exposing ( V )

                import limits ( maxLen )

                data V = String
                    invariant String.length(value) <= maxLen
                """)));
    }

    @Test
    void anInvariantCallsAnImportedHelper() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(LIMITS, """
                module ids exposing ( V )

                import limits ( fits )

                data V = String
                    invariant fits(value)
                """)));
    }

    /** The substituted value is what the rule is checked against: a construction the limit rejects
     * is rejected, and the limit is the declaring module's. */
    @Test
    void theImportedValueIsWhatTheRuleIsCheckedAgainst() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of(LIMITS, """
                module ids exposing ( V )

                import limits ( maxLen )

                data V = String
                    invariant String.length(value) <= maxLen
                """)), getClass().getClassLoader());

        assertEquals("abc", Codecs.encode(loader, "ids.V", Codecs.decoded(loader, "ids.V", "abc")));
        assertEquals("Err", Codecs.decode(loader, "ids.V", "abcd").getClass().getSimpleName());
    }

    /** A published helper means what it meant where it was written, in an invariant as in a body:
     * {@code fits} rests on the limit its own module wrote, not on the one the reader spells the same
     * way. */
    @Test
    void anImportedHelperKeepsItsOwnDependenciesWhenTheReaderSharesTheirNames() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of(LIMITS, """
                module ids exposing ( V )

                import limits ( fits )

                let maxLen = 99

                data V = String
                    invariant fits(value)
                """)), getClass().getClassLoader());

        assertEquals("Err", Codecs.decode(loader, "ids.V", "abcd").getClass().getSimpleName());
    }

    /** An unexposed value has no name here, in an invariant as anywhere else. */
    @Test
    void anUnpublishedValueCannotBeNamedInAnInvariant() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module limits exposing ( fits )

                        let maxLen = 3

                        let fits (s: String) : Bool = String.length(s) <= maxLen
                        """, """
                        module ids exposing ( V )

                        import limits ( maxLen )

                        data V = String
                            invariant String.length(value) <= maxLen
                        """)));

        assertTrue(e.getMessage().contains("maxLen"), e.getMessage());
    }

    /**
     * The discharge analysis reads the clause with the imported bound substituted, so a construction
     * the bound rejects is proven to violate rather than left as a rule the check cannot read.
     */
    @Test
    void anImportedBoundIsReadByTheDischargeAnalysis() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module limits exposing ( floor )

                        let floor = 0m
                        """, """
                        module money exposing ( Money, calc )

                        import limits ( floor )

                        data Money = Decimal
                            invariant value >= floor

                        behavior calc : (m: Money) -> Money constructs Money
                        let calc (m) = Money(0m) - Money(1m)
                        """)));

        assertEquals("E2010", e.diagnostic().code(), e.getMessage());
    }

    /** The invariant travels as written, so the module it names is one the reading project needs on
     * its class path — and reading it there is what makes the name resolve. */
    @Test
    void anImportedValueInAnInvariantCrossesAProjectBoundary() throws Exception {
        Map<String, byte[]> upstream = Compiler.compile(LIMITS);
        ModulePath path = upstream::get;

        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module app.ids exposing ( V )

                import limits ( maxLen )

                data V = String
                    invariant String.length(value) <= maxLen
                """), path));
    }
}
