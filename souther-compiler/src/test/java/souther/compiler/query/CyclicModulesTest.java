package souther.compiler.query;

import souther.compiler.diag.Located;
import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Modules that name each other are rejected, and rejecting them is where it stops.
 *
 * <p>A cycle is the one thing that makes the questions below it unanswerable in the strict sense:
 * what a module's behaviors are typed as depends on the module it names, which depends on this one.
 * Reporting the cycle and then compiling anyway asks that question and gets no answer.
 *
 * <p>The editor path is what this is about. A batch compile stops at the first structural problem,
 * so it never reached the rest; an editor reports everything and carries on, and had to be told
 * where to stop.
 */
class CyclicModulesTest {

    private static final String A = """
            module m.a exposing ( A )
            import m.b ( B )
            data A = { b: B }
            """;

    private static final String B = """
            module m.b exposing ( B )
            import m.a ( A )
            data B = String
            """;

    /** Two modules whose behaviors name each other, qualified — no import line written. */
    private static final String X = """
            module cyc.x exposing ( A, B, f, g : B )
            data A = { n: Int }
            data B = { n: Int }
            behavior f : (a: A) -> B constructs B
            let f (a) = B { n = a.n }
            behavior g = cyc.y.h >-> f
            """;

    private static final String Y = """
            module cyc.y exposing ( A, h, k : A )
            data A = { n: Int }
            behavior h : (a: A) -> A constructs A
            let h (a) = A { n = a.n }
            behavior k = cyc.x.f >-> h
            """;

    private static Map<String, String> documents(String first, String second) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("first.sou", first);
        byId.put("second.sou", second);
        return byId;
    }

    @Test
    void anEditorIsToldAboutACycleThroughImports() {
        Map<String, List<Diagnostic>> found =
                Located.diagnosticsOf(Compiler.diagnoseModules(documents(A, B), Set.of()));

        assertTrue(found.values().stream().flatMap(List::stream)
                        .anyMatch(d -> "E1501".equals(d.code())),
                "the editor reports the cycle, as the batch compiler does");
    }

    @Test
    void anEditorIsToldAboutACycleThroughQualifiedBehaviorReferences() {
        // Neither module writes an import line; each names the other's behavior as a stage. That is
        // the same cycle, and following only the import lines would not see it.
        Map<String, List<Diagnostic>> found =
                Located.diagnosticsOf(Compiler.diagnoseModules(documents(X, Y), Set.of()));

        assertTrue(found.values().stream().flatMap(List::stream)
                        .anyMatch(d -> "E1501".equals(d.code())),
                "a cycle written without an import line is still a cycle");
    }

    @Test
    void nothingIsCompiledOutOfACycle() {
        Compilation compilation = Compilation.ofDocuments(documents(X, Y), Set.of(),
                souther.compiler.meta.ModulePath.EMPTY);
        compilation.diagnostics();

        assertEquals(Map.of(), compilation.classes(),
                "a module whose signatures cannot be worked out emits nothing");
        assertTrue(compilation.db().isComputed(new Output.All()),
                "the cycle is stopped before anything asks a question that answers itself, so the"
                        + " answers above it are kept rather than redone on every ask");
    }

    @Test
    void whatAModuleReachesIsWorkedOutWithoutAskingAboutEachModuleReached() {
        Compilation compilation = Compilation.ofDocuments(documents(A, B), Set.of(),
                souther.compiler.meta.ModulePath.EMPTY);
        compilation.diagnostics();

        Output.Reaches reaches = new Output.Reaches("m.a");
        assertEquals(List.of("m.a", "m.b"), compilation.db().ask(reaches).value(),
                "the walk follows the imports round to a module it has seen and stops there");
        assertTrue(compilation.db().isComputed(reaches),
                "it answered without being asked through itself, so the answer is kept — a walk"
                        + " that asked about each module it reached would be one of these two"
                        + " modules asking what it reaches through the other");
    }

    @Test
    void aBatchCompileStopsAtTheCycle() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(A, B)));
        assertEquals("E1501", e.diagnostic().code());
    }
}
