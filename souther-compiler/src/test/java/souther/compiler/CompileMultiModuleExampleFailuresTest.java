package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A change to a widely-imported data breaks examples in every module that writes a fixture of it, and
 * all of them are reported in one compile. Each module used to throw as it was reached, so learning
 * how far a one-field change reached took as many edit-and-recompile rounds as there were modules
 * (issue #114) — the question an author has after touching a shared type is exactly the one those
 * rounds withheld.
 *
 * <p>Each diagnostic carries the source it came from, so a renderer quotes each module's own file
 * rather than the first one's.
 */
class CompileMultiModuleExampleFailuresTest {

    /** `Line` gains a field none of the three downstream fixtures writes. */
    private static final String SHARED = """
            module shared exposing ( Line, Bag, Sum, total )
            data Line = { sku: String, qty: Int, weight: Int }
            data Bag = { lines: List<Line> }
            data Sum = { n: Int }
            behavior total : (b: Bag) -> Sum constructs Sum
            let total (b) = Sum { n = List.length(b.lines) }
            example total
              | "counts" : (Bag { lines = [ Line { sku = "a", qty = 1 } ] }) -> Sum { n = 1 }
            """;
    private static final String ONE = """
            module one
            import shared ( Line )
            data OneOut = { n: Int }
            behavior one : (l: Line) -> OneOut constructs OneOut
            let one (l) = OneOut { n = l.qty }
            example one
              | "reads the qty" : (Line { sku = "a", qty = 2 }) -> OneOut { n = 2 }
            """;
    private static final String TWO = """
            module two
            import shared ( Line )
            data TwoOut = { s: String }
            behavior two : (l: Line) -> TwoOut constructs TwoOut
            let two (l) = TwoOut { s = l.sku }
            example two
              | "reads the sku" : (Line { sku = "b", qty = 1 }) -> TwoOut { s = "b" }
            """;

    @Test
    void everyModuleWithAStaleFixtureIsReportedInOneCompile() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(SHARED, ONE, TWO)));

        assertEquals(3, e.diagnostics().size(),
                "one row per module, not the first module's alone: " + e.diagnostics().size());
        for (Diagnostic d : e.diagnostics()) {
            assertEquals("E1005", d.code());
        }
    }

    @Test
    void eachDiagnosticNamesTheSourceItCameFrom() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(SHARED, ONE, TWO)));

        Set<String> named = java.util.stream.IntStream.range(0, e.diagnostics().size())
                .mapToObj(e::sourceIdOf)
                .collect(Collectors.toSet());

        assertEquals(Set.of("0", "1", "2"), named,
                "three modules, three sources — a renderer quotes each one's own file");
    }

    @Test
    void aSingleModuleFailureStillNamesItsOwnSource() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(SHARED, """
                        module clean
                        import shared ( Line )
                        data CleanOut = { n: Int }
                        behavior clean : (l: Line) -> CleanOut constructs CleanOut
                        let clean (l) = CleanOut { n = l.qty }
                        """)));

        assertEquals(1, e.diagnostics().size());
        assertEquals("0", e.sourceId(), "the stale fixture is in the first source");
    }

    @Test
    void everyModulesExamplesHoldingIsStillASuccessfulCompile() {
        Compiler.compileModules(List.of("""
                module shared exposing ( Line )
                data Line = { sku: String, qty: Int }
                """, """
                module one
                import shared ( Line )
                data OneOut = { n: Int }
                behavior one : (l: Line) -> OneOut constructs OneOut
                let one (l) = OneOut { n = l.qty }
                example one
                  | "reads the qty" : (Line { sku = "a", qty = 2 }) -> OneOut { n = 2 }
                """));
    }

}
