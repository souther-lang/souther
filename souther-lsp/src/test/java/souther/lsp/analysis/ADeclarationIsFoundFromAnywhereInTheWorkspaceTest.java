package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.WorkspaceSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name is looked for across the workspace, and what a module offers is looked for through the
 * module. The two are the same fact reached from opposite ends — what a file declares — and neither
 * asks a body to have compiled.
 */
class ADeclarationIsFoundFromAnywhereInTheWorkspaceTest {

    private static final String LIB_URI = "file:///lib.sou";
    private static final String MODEL_URI = "file:///m.sou";

    private static final String LIB = """
            module lib exposing ( Cost, priced )

            data Cost = { amount: Int }
            data Hidden = { v: Int }

            behavior priced : (c: Cost) -> Int
            let priced (c) = c.amount
            """;

    private static final String MODEL = """
            module m

            import lib as l ( Cost )

            behavior submit : (c: Cost) -> Int
            let submit (c) = c.amount
            """;

    @Test
    void aDeclarationIsFoundInWhicheverFileWroteIt() {
        List<String> found = namesOf(symbols("Cost"));

        assertEquals(List.of("Cost"), found, "one file declares it, and it is found there");
        assertEquals(LIB_URI, symbols("Cost").getFirst().location().uri());
    }

    @Test
    void theSearchIgnoresCase() {
        assertEquals(List.of("Cost"), namesOf(symbols("cost")));
    }

    @Test
    void anEmptyQueryNamesEverythingDeclared() {
        List<String> found = namesOf(symbols(""));

        assertTrue(found.containsAll(List.of("Cost", "Hidden", "priced", "submit")),
                "every declaration of every file, found: " + found);
        assertFalse(found.contains("amount"), "a field is reached by opening what holds it");
    }

    /**
     * And a file that will not compile is searched like any other.
     *
     * <p>Which is the case an author is in when they go looking: they are in the middle of writing
     * one file and want to reach a declaration in another.
     */
    @Test
    void aFileThatWillNotCompileIsSearchedAllTheSame() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(LIB_URI, LIB);
        sources.put(MODEL_URI, MODEL + "\nlet broken (x) = x.");

        assertEquals(List.of("Cost"), namesOf(symbolsIn(sources, "Cost")));
    }

    /** And what a module offers, offered through the alias that reaches it. */
    @Test
    void aModuleOffersWhatItExposesAndNotWhatItKeeps() {
        List<String> offered = labelsOf(afterTheDotOn(MODEL + "\nlet other (x) = l.\n"));

        assertEquals(List.of("Cost", "priced"), offered,
                "`lib` exposes those two; `Hidden` is not one of them");
    }

    /**
     * And the language's own library is a namespace like any other.
     *
     * <p>It carries no bare names — everything in it is reached through a qualifier — so a member
     * list after {@code List.} is not a fringe of this question but most of it. What is offered is
     * its published surface, which is the set of qualified names a module outside the reserved
     * namespace may write.
     */
    @Test
    void theLibraryOffersWhatItPublishesUnderTheQualifier() {
        List<String> offered = labelsOf(afterTheDotOn(MODEL + "\nlet other (x) = List.\n"));

        assertFalse(offered.isEmpty(), "`List.` is where a library name is written");
        assertTrue(offered.contains("map"), "found: " + offered);
        for (String each : offered) {
            assertFalse(each.contains("."), each + " is reached under its own qualifier");
        }
    }

    @Test
    void whatIsOfferedIsPaintedAsWhatItIs() {
        List<CompletionItem> offered = afterTheDotOn(MODEL + "\nlet other (x) = l.\n");

        assertEquals(CompletionItem.CLASS, offered.getFirst().kind(), "`Cost` is a data");
        assertEquals(CompletionItem.INTERFACE, offered.get(1).kind(), "`priced` is a behavior");
    }

    private static List<String> namesOf(List<WorkspaceSymbol> symbols) {
        List<String> names = new ArrayList<>();
        for (WorkspaceSymbol each : symbols) {
            names.add(each.name());
        }
        return names;
    }

    private static List<String> labelsOf(List<CompletionItem> items) {
        List<String> labels = new ArrayList<>();
        for (CompletionItem item : items) {
            labels.add(item.label());
        }
        return labels;
    }

    private static List<WorkspaceSymbol> symbols(String query) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(LIB_URI, LIB);
        sources.put(MODEL_URI, MODEL);
        return symbolsIn(sources, query);
    }

    private static List<WorkspaceSymbol> symbolsIn(Map<String, String> sources, String query) {
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        return analyzer.workspaceSymbols(query, graph);
    }

    private static List<CompletionItem> afterTheDotOn(String text) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(LIB_URI, LIB);
        sources.put(MODEL_URI, text);
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);

        List<String> lines = text.lines().toList();
        int on = lines.size() - 1;
        return analyzer.completions(MODEL_URI, new Position(on, lines.get(on).length()), graph);
    }
}
