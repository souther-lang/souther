package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name that denotes nothing is reported and the compiler carries on.
 *
 * <p>It denotes an error type instead of ending the module. That type absorbs, so the one mistake is
 * reported once rather than again at every position the value it produced flowed into — and the rest
 * of the module is read, so an author is told about every unknown name at once instead of one per
 * compile.
 */
class UnresolvedNamesTest {

    private static List<Diagnostic> diagnose(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", source);
        return Compiler.diagnoseModules(byId, Set.of()).get("a.sou");
    }

    @Test
    void everyUnknownNameIsReportedAtOnce() {
        List<Diagnostic> found = diagnose("""
                module m.a

                data A = { one: Nowhere, two: Elsewhere }
                """);

        assertEquals(2, found.size(), "both, not the first: " + found);
        assertTrue(found.stream().anyMatch(d -> d.args() != null
                && List.of(d.args()).contains("Nowhere")));
        assertTrue(found.stream().anyMatch(d -> d.args() != null
                && List.of(d.args()).contains("Elsewhere")));
    }

    @Test
    void oneMistakeIsNotReportedAtEveryPlaceTheValueWent() {
        // `total` has no type, so every position it flows into could disagree with it. None does:
        // an error type is assignable both ways.
        List<Diagnostic> found = diagnose("""
                module m.a exposing ( Order, price )

                data Order = { total: Nowhere }

                behavior price : (o: Order) -> Int
                let price (o) = o.total
                """);

        assertEquals(1, found.size(), "the unknown name, and nothing downstream of it: " + found);
    }

    @Test
    void aModuleWithATypeNobodyCanNameEmitsNothing() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", """
                module m.a

                data A = { one: Nowhere }
                """);
        Compilation c = Compilation.ofDocuments(byId, Set.of(),
                souther.compiler.meta.ModulePath.EMPTY);
        c.diagnostics();

        assertEquals(Map.of(), c.classes(),
                "there is no bytecode for a type nobody could name");
    }
}
