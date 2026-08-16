package souther.compiler.query;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Assembling a module's scope reads what it needs of the modules around it, and no more.
 *
 * <p>What a universe says under a name is asked one name at a time so that a compilation reaching
 * no other module reads none. What it says is asked the same way: a question that is not about the
 * module named is a reason to work this module's scope out again that has nothing to do with this
 * module.
 *
 * <p>Measured as what was computed rather than as what came out. An answer that is worked out again
 * and comes out the same stops there, so nothing below sees it — and the work is done all the same,
 * in every module that imports the one that was edited.
 */
class WhatAScopeReadsOfTheModulesAroundItTest {

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

    /** A module that writes a library import line, and one that imports a type from it. */
    private static final String BRINGS_IN_A_LIBRARY_NAME = """
            module scope.money exposing ( Amount )
            import String ( length )
            data Amount = String
                invariant length(value) > 0
            """;

    private static final String IMPORTS_THE_TYPE = """
            module scope.order exposing ( Order )
            import scope.money ( Amount )
            data Order = { total: Amount }
            """;

    /**
     * What another module's import lines let <em>it</em> write bare is not read.
     *
     * <p>Nothing a reader writes is answered by that table, and reading it anyway puts every
     * importing module's scope behind an edit to a library import line in a module it imports
     * from — which is the projection {@code Front.Exposed} and {@code Front.LibraryNames} were
     * split into to avoid.
     */
    @Test
    void theLibraryNamesOfAModuleImportedFromAreNotRead() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("money.sou", BRINGS_IN_A_LIBRARY_NAME);
        byId.put("order.sou", IMPORTS_THE_TYPE);
        Compilation compilation = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        assertTrue(compilation.db().ask(new Names.ModuleScope("scope.order")).present());

        assertTrue(compilation.db().isComputed(new Front.LibraryNames("scope.order")),
                "the module being scoped writes bare what its own import lines brought in");
        assertFalse(compilation.db().isComputed(new Front.LibraryNames("scope.money")),
                "and nothing it writes is answered by what the module it imports from may write"
                        + " bare");
    }

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
