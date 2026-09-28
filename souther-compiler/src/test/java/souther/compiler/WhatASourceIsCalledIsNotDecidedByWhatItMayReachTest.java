package souther.compiler;

import souther.compiler.CompilationSources.SourceFile;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Located;
import souther.compiler.diag.SourceContext;
import souther.compiler.diag.SourceContextResolver;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a source is called and what its imports may reach are two questions, and neither answers the
 * other.
 *
 * <p>A lone source with no {@code module} header is named after its file, or {@code Main} with no
 * file; a source that writes a header is called what it says. Which modules an import reaches is the
 * path's to say. So each row below crosses the two — a header or none, a path holding the module it
 * imports or none — and each names the module it expects, so a row that compiled under the wrong
 * name fails rather than passes.
 */
class WhatASourceIsCalledIsNotDecidedByWhatItMayReachTest {

    private static final String LIBRARY = """
            module shared.money exposing ( Amount )
            data Amount = Int
                invariant value >= 0
            """;

    private static final String HEADERLESS = """
            data Order = { total: Int }
            """;

    private static final String HEADERLESS_IMPORTING = """
            import shared.money ( Amount )
            data Order = { total: Amount }
            """;

    private static final String NAMED = """
            module app.order
            data Order = { total: Int }
            """;

    private static final String NAMED_IMPORTING = """
            module app.order exposing ( Order )
            import shared.money ( Amount )
            data Order = { total: Amount }
            """;

    private static final String NAMED_BESIDE = """
            module app.invoice
            import shared.money ( Amount )
            import app.order ( Order )
            data Invoice = { order: Order, total: Amount }
            """;

    private static ModulePath library() {
        return ModulePath.of(Compiler.compile(LIBRARY));
    }

    private static Set<String> classesOf(CompilationSources sources, ModulePath path) {
        return Compiler.compiled(sources, path, new ArrayList<>(), Adequacy.Asked.NOTHING)
                .classes().keySet();
    }

    private static CompilationSources file(String path, String text) {
        return CompilationSources.files(List.of(new SourceFile(path, text)));
    }

    @Test
    void aLoneHeaderLessFileIsNamedAfterItself() {
        Set<String> classes = classesOf(file("src/orders.sou", HEADERLESS), ModulePath.EMPTY);

        assertTrue(classes.contains("orders.Order"), classes::toString);
    }

    @Test
    void aLoneHeaderLessFileKeepsItsNameWhenItImportsOffThePath() {
        Set<String> classes = classesOf(file("src/orders.sou", HEADERLESS_IMPORTING), library());

        assertTrue(classes.contains("orders.Order"), classes::toString);
    }

    @Test
    void aLoneFileThatNamesItselfIsCalledWhatItSays() {
        Set<String> classes = classesOf(file("src/orders.sou", NAMED), ModulePath.EMPTY);

        assertTrue(classes.contains("app.order.Order"), classes::toString);
    }

    @Test
    void aLoneFileThatNamesItselfIsCalledWhatItSaysWhenItImportsOffThePath() {
        Set<String> classes = classesOf(file("src/orders.sou", NAMED_IMPORTING), library());

        assertTrue(classes.contains("app.order.Order"), classes::toString);
    }

    @Test
    void severalFilesThatNameThemselvesLinkAndImportOffThePath() {
        Set<String> classes = classesOf(CompilationSources.files(List.of(
                new SourceFile("src/order.sou", NAMED_IMPORTING),
                new SourceFile("src/invoice.sou", NAMED_BESIDE))), library());

        assertTrue(classes.contains("app.order.Order"), classes::toString);
        assertTrue(classes.contains("app.invoice.Invoice"), classes::toString);
    }

    @Test
    void oneOfSeveralFilesMayNotLeaveItsHeaderOff() {
        assertThrows(CompileException.class, () -> classesOf(CompilationSources.files(List.of(
                new SourceFile("src/order.sou", NAMED),
                new SourceFile("src/orders.sou", HEADERLESS))), ModulePath.EMPTY));
    }

    @Test
    void aModuleSetOfOneStillHasToNameItself() {
        assertThrows(CompileException.class, () -> classesOf(
                CompilationSources.modules(List.of(HEADERLESS)), ModulePath.EMPTY));
    }

    @Test
    void aTextWithNoFileIsCalledMain() {
        Set<String> classes = classesOf(CompilationSources.text(HEADERLESS), ModulePath.EMPTY);

        assertTrue(classes.contains(ImplicitModuleName.OF_A_TEXT + ".Order"), classes::toString);
    }

    @Test
    void theFileNameIsTheLastSegmentOnEitherSeparator() {
        assertTrue(classesOf(file("a\\b\\orders.sou", HEADERLESS), ModulePath.EMPTY)
                .contains("orders.Order"));
    }

    @Test
    void anAnalysisNamesTheLoneFileTheWayACompileDoes() {
        List<Located> warnings = new ArrayList<>();
        Compilation analyzed = Compiler.analyzed(file("src/orders.sou", HEADERLESS_IMPORTING),
                library(), warnings, Adequacy.Asked.NOTHING);

        assertEquals(List.of("orders"), analyzed.modules());
        assertEquals(List.of(), analyzed.errors());
    }

    /**
     * A diagnostic about a source these were not is quoted from none of them, however few there are.
     * One file is not the answer to an id that is not its id.
     */
    @Test
    void anIdThatIsNoneOfTheSourcesIsQuotedFromNone() {
        SourceContextResolver contexts = file("src/orders.sou", HEADERLESS).contexts();

        SourceContext own = contexts.sourceOf(Compilation.idOfSourceIndex(0));
        assertEquals("orders.sou", own.fileName());
        assertEquals(HEADERLESS, own.text());
        assertNull(contexts.sourceOf(new SourceId("elsewhere.sou")));
        assertNull(contexts.sourceOf(Compilation.idOfSourceIndex(1)));
        assertNull(contexts.sourceOf(null));
    }
}
