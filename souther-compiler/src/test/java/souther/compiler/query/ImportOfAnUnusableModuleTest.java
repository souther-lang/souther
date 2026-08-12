package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.diag.Located;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Importing a module that is here but cannot be used.
 *
 * <p>"Not part of this compilation" and "part of it and saying nothing usable" are different things,
 * and only the first is the importer's business. Telling an importer that a module it can see is
 * unknown sends the author to a file that is fine.
 */
class ImportOfAnUnusableModuleTest {

    /** Takes a name the compiler ships, which no source may. */
    private static final String RESERVED = """
            module souther.evil exposing ( X )

            data X = Int
            """;

    private static final String IMPORTER = """
            module app.main

            import souther.evil ( X )

            data A = { x: X }
            """;

    @Test
    void theImporterIsNotToldTheModuleIsUnknown() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("evil.sou", RESERVED);
        byId.put("main.sou", IMPORTER);
        Map<String, List<Diagnostic>> found = Located.diagnosticsOf(Compiler.diagnoseModules(byId, Set.of()));

        assertEquals(1, found.get("evil.sou").size(),
                "the module that took a reserved name is what is wrong: " + found.get("evil.sou"));
        assertTrue(found.get("evil.sou").stream()
                        .anyMatch(d -> d.said() instanceof ModuleMessage.TheModuleIsInTheReservedNamespace));
        assertEquals(List.of(), found.get("main.sou"),
                "app.main can see the module; what is wrong with it is not app.main's to hear: "
                        + found.get("main.sou"));
    }
}
