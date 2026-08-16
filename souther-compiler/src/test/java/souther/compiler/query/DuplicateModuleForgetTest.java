package souther.compiler.query;

import souther.compiler.source.SourceId;

import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Closing one of two sources that claim the same module name.
 *
 * <p>Forgetting a source drops the answers about the module it declared, and while two sources claim
 * one name only one of them is the module — so those answers were all about the one being closed.
 * The other source becomes the module and is answered afresh.
 */
class DuplicateModuleForgetTest {

    private static final String FIRST = """
            module shop.cart exposing ( Total )

            data Total = Int
            """;

    private static final String SECOND = """
            module shop.cart exposing ( Total, Extra )

            data Total = String

            data Extra = Int
            """;

    @Test
    void theSurvivorBecomesTheModule() {
        Map<String, String> both = new LinkedHashMap<>();
        both.put("a.sou", FIRST);
        both.put("b.sou", SECOND);
        Compilation c = Compilation.ofDocuments(both, Set.of(), ModulePath.EMPTY);
        Map<SourceId, List<souther.compiler.diag.Diagnostic>> first = Located.diagnosticsOf(c.diagnostics());
        assertEquals(1, first.get(new SourceId("b.sou")).size(), "the second claim is the one reported");

        Map<String, String> onlySecond = new LinkedHashMap<>();
        onlySecond.put("b.sou", SECOND);
        c.update(onlySecond, Set.of());

        assertEquals(List.of(), Located.diagnosticsOf(c.diagnostics()).get(new SourceId("b.sou")),
                "b.sou is the module now, and there is nothing wrong with it");
        assertTrue(c.classes().containsKey("shop.cart.Extra"),
                "what is compiled is what b.sou declares, not what a.sou did");
    }
}
