package souther.compiler.query;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name nothing here has is answered by nothing here having it.
 *
 * <p>What a universe says under a name is asked one name at a time so that a compilation reaching
 * no other module reads none. A misspelt import is the case where there is nothing to read, and it
 * has to stay that way: what a module declares is refused when the module is in an import cycle,
 * and whether it is in one is worked out over every module the workspace declares. Asked of a name
 * nothing has, that puts the shape of the whole workspace behind one module's answer about its own
 * header — so an edit anywhere would be a reason to work out again what a module with a typo in an
 * import line means.
 */
class AnUnknownModuleIsNotLookedForInTheDeclarationWorldTest {

    private static final String NAMES_ONE_THAT_IS_NOT_THERE = """
            module app.order exposing ( Order )
            import shared.money ( Amount )
            data Order = { total: Amount }
            """;

    /** A second module, so that there is a workspace to have a shape. */
    private static final String BESIDE_IT = """
            module app.note exposing ( Note )
            data Note = { text: String }
            """;

    @Test
    void whatIsNotThereIsNotLookedUpAmongTheDeclarations() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("order.sou", NAMES_ONE_THAT_IS_NOT_THERE);
        byId.put("note.sou", BESIDE_IT);
        Compilation compilation = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        compilation.diagnostics();

        assertTrue(compilation.db().isComputed(new Names.ModuleScope("app.order")),
                "the module was scoped, so the import line was read");
        assertFalse(compilation.db().isComputed(new Names.Declarations("shared.money")),
                "there is no module of that name, and asking what it declares is asking whether it"
                        + " is in an import cycle — a question about every module there is");
    }
}
