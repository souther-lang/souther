package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.diag.Located;
import souther.compiler.diag.Diagnostic;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What follows from a name that denotes nothing is not reported again.
 *
 * <p>An absorbing type answers a comparison. It cannot answer a check that wants a particular shape —
 * Int or Decimal to add, two lists or two strings to append — and letting one through puts the error
 * type's own rendering in the message, which names nothing an author could look for. Those definitions
 * are abandoned instead.
 */
class CascadeStopsAtTheCauseTest {

    private static Map<String, List<Diagnostic>> diagnose(Map<String, String> byId) {
        return Located.diagnosticsOf(Compiler.diagnoseModules(byId, Set.of()));
    }

    private static Map<String, String> one(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", source);
        return byId;
    }

    @Test
    void anOperandWithNoTypeIsNotReportedAsTheWrongType() {
        List<Diagnostic> found = diagnose(one("""
                module m.a exposing ( A, f, g )

                data A = { n: Nowhere }

                behavior f : (a: A) -> Int
                let f (a) = a.n + a.n

                behavior g : (a: A) -> String
                let g (a) = "x" ++ a.n
                """)).get("a.sou");

        assertEquals(1, found.size(),
                "the name that denotes nothing, and nothing about adding or appending it: " + found);
        assertFalse(found.stream().anyMatch(d -> List.copyOf(d.values().values()).contains("?")),
                "the error type's own rendering never reaches a message: " + found);
    }

    @Test
    void aModuleBuiltAgainstARejectedOneIsNotEmitted() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("dup.sou", """
                module m.dup exposing ( A )

                data A = Int

                data A = String
                """);
        byId.put("a.sou", """
                module m.a exposing ( B )

                import m.dup ( A )

                data B = { a: A }
                """);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        Map<String, List<Diagnostic>> found = Located.diagnosticsOf(c.diagnostics());

        assertEquals(1, found.get("dup.sou").size(), "the duplicate: " + found.get("dup.sou"));
        assertEquals(List.of(), found.get("a.sou"),
                "m.a is correct, and is told nothing: " + found.get("a.sou"));
        assertEquals(Map.of(), c.classes(),
                "m.a is built against declarations nothing will emit, so it is not emitted either");
    }

    @Test
    void anImportThatWorksTakesANameAFailedOneOnlyStoodInFor() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("good.sou", """
                module m.good exposing ( X )

                data X = Int
                """);
        byId.put("a.sou", """
                module m.a exposing ( B )

                import m.nope ( X )
                import m.good ( X )

                data B = { x: X }
                """);
        List<Diagnostic> found = diagnose(byId).get("a.sou");

        assertEquals(1, found.size(),
                "the import line that names nothing, and no conflict with it: " + found);
        assertTrue(found.stream()
                        .anyMatch(d -> d.said() instanceof ModuleMessage.UnknownModule),
                "which line is wrong: " + found);
    }

    /**
     * A hole can sit somewhere no walk of the declarations would find it — a local annotation in a
     * body — and with nothing reported here to say so, when the caller is holding the other file back.
     * An import that cannot be followed is what makes the module unsound, wherever the hole ends up.
     */
    @Test
    void animportThatCannotBeFollowedIsEnoughOnItsOwn() {
        Compilation c = Compilation.ofDocuments(one("""
                module m.a exposing ( Out, f )

                import m.broken ( X )

                data Out = { v: Int }

                behavior f : (n: Int) -> Out constructs Out
                let f (n) = {
                    let x: X = n
                    Out { v = n }
                }
                """), Set.of("m.broken"), ModulePath.EMPTY);
        Located.diagnosticsOf(c.diagnostics());

        assertFalse(Boolean.TRUE.equals(c.db().ask(new Names.Sound("m.a")).value()),
                "m.a is built on a name nothing brought in");
        assertEquals(Map.of(), c.classes());
    }
}
