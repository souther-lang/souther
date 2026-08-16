package souther.lsp.analysis;

import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.Position;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Completion asks the workspace compile which bare spelling reaches what, and goes on offering the
 * names that came from elsewhere while the document being typed in will not parse.
 *
 * <p>The two halves are asymmetric on purpose. What the document declares is read off its own tree
 * every time, so a definition being written is offered before it compiles; what reaches it from
 * elsewhere is the compiler's answer, kept per document because a module is not one file.
 */
class WhatMayBeWrittenHereIsAskedOfTheCompileTest {

    private static final String UP = """
            module up exposing ( Amount, Colour, price )

            data Amount = { v: Int }

            data Colour = Red | Green

            let price = 100
            """;

    private static final String DOWN = """
            module down

            import up ( Amount, Colour, price )
            import String ( length )

            data Own = { n: Int }

            behavior f : (x: Int) -> Int
            let f (x) = x
            """;

    private static final String UP_URI = "file:///up.sou";
    private static final String DOWN_URI = "file:///down.sou";

    /** The cursor in the body of `let f (x) = x`, which is the last line of {@link #DOWN}. */
    private static final Position IN_THE_BODY = new Position(8, 12);

    private static ModuleGraph graphOf(String... uriThenText) {
        Map<String, String> sources = new LinkedHashMap<>();
        for (int i = 0; i < uriThenText.length; i += 2) {
            sources.put(uriThenText[i], uriThenText[i + 1]);
        }
        return ModuleGraph.of(sources);
    }

    private static Map<String, CompletionItem> byLabel(List<CompletionItem> items) {
        Map<String, CompletionItem> out = new LinkedHashMap<>();
        for (CompletionItem item : items) {
            out.put(item.label(), item);
        }
        return out;
    }

    /** The candidates that came from another module or from the library — everything carrying an
     * origin that is not this document's own module, plus what the standard library published. */
    private static List<String> fromElsewhere(List<CompletionItem> items, String ownModule) {
        List<String> out = new ArrayList<>();
        for (CompletionItem item : items) {
            if (item.detail() != null && !item.detail().equals(ownModule)) {
                out.add(item.label());
            }
        }
        return out;
    }

    /** {@link #DOWN} with a line of nonsense inserted before the body, which no recovery makes into
     * a module: the file is held out of the compile, and the compiler has nothing to say about it. */
    private static String broken(String source) {
        return source.replace("let f (x) = x", "let f (x) = ((((\nlet f (x) = x");
    }

    @Test
    void aNameAnImportBringsInIsOfferedAsWhatItIsDeclaredToBe() {
        Analyzer analyzer = new Analyzer();
        Map<String, CompletionItem> items = byLabel(analyzer.completions(
                DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, DOWN)));

        assertEquals(new CompletionItem("Amount", CompletionItem.CLASS, "up"), items.get("Amount"),
                "an imported product data, as a data and as coming from up: " + items.keySet());
        assertEquals(new CompletionItem("Colour", CompletionItem.ENUM, "up"), items.get("Colour"),
                "an imported sum is offered as a sum, not as a product");
        assertEquals(new CompletionItem("price", CompletionItem.FUNCTION, "up"), items.get("price"),
                "a value another module publishes");
        assertEquals(new CompletionItem("length", CompletionItem.FUNCTION, "String"),
                items.get("length"), "a library name an import let this module write bare");
        assertEquals(new CompletionItem("Own", CompletionItem.CLASS, "down"), items.get("Own"),
                "this document's own declaration, under its own module");
        assertEquals(CompletionItem.VARIABLE, items.get("x").kind(), "the param in scope");
        assertEquals(CompletionItem.KEYWORD, items.get("behavior").kind(), "a language keyword");
    }

    @Test
    void namesFromElsewhereAreOfferedWhileTheDocumentWillNotParse() {
        Analyzer analyzer = new Analyzer();
        List<CompletionItem> clean = analyzer.completions(
                DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, DOWN));
        assertFalse(fromElsewhere(clean, "down").isEmpty(), "the clean document reaches names");

        List<CompletionItem> whileBroken = analyzer.completions(
                DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, broken(DOWN)));

        List<String> elsewhere = fromElsewhere(whileBroken, "down");
        assertFalse(elsewhere.isEmpty(),
                "a document that will not parse still reaches what it reached: " + elsewhere);
        assertTrue(elsewhere.containsAll(List.of("Amount", "Colour", "price", "length")),
                "each of them, whichever namespace it came from: " + elsewhere);
    }

    /**
     * The negative control for the test above: it is the remembered answer doing the work, and
     * nothing else. Asked about a document that has never parsed since this server started, there is
     * nothing from elsewhere to offer — which is what the state was for every document before.
     */
    @Test
    void withNoCompileThatEverAnsweredThereIsNothingFromElsewhere() {
        Analyzer analyzer = new Analyzer();
        List<CompletionItem> items = analyzer.completions(
                DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, broken(DOWN)));

        assertEquals(List.of(), fromElsewhere(items, "down"),
                "nothing answered about this document, so nothing is remembered about it");
        assertTrue(byLabel(items).containsKey("Own"),
                "what the document declares is still read off its own tree");
    }

    @Test
    void aDefinitionBeingTypedIsOfferedBeforeItCompiles() {
        Analyzer analyzer = new Analyzer();
        analyzer.completions(DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, DOWN));

        String beingTyped = broken(DOWN).replace("data Own", "data Fresh = { m: Int }\n\ndata Own");
        Map<String, CompletionItem> items = byLabel(analyzer.completions(
                DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, beingTyped)));

        assertTrue(items.containsKey("Fresh"),
                "written into a document that will not parse, and offered: " + items.keySet());
        assertTrue(items.containsKey("Amount"), "and the remembered names are still there");
    }

    /**
     * What this document declares is kept out of what is remembered about it, rather than filtered
     * on the way out. A name it no longer writes is in neither place, so renaming a definition while
     * the file will not parse does not go on offering the name it had.
     */
    @Test
    void aDeclarationRenamedWhileTheDocumentWillNotParseIsNotOfferedUnderItsOldName() {
        Analyzer analyzer = new Analyzer();
        analyzer.completions(DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, DOWN));

        String renamed = broken(DOWN).replace("data Own", "data Owned");
        Map<String, CompletionItem> items = byLabel(analyzer.completions(
                DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, renamed)));

        assertTrue(items.containsKey("Owned"), "under what it is called now: " + items.keySet());
        assertFalse(items.containsKey("Own"), "and not under what it was called");
        assertTrue(items.containsKey("Amount"), "the names from elsewhere are unaffected");
    }

    /**
     * The remembered answer is never consulted while the compiler can answer, so an import taken out
     * of a document that parses takes its names with it at once.
     */
    @Test
    void anImportRemovedFromADocumentThatParsesStopsBeingOffered() {
        Analyzer analyzer = new Analyzer();
        analyzer.completions(DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, DOWN));

        String withoutTheImport = DOWN.replace("import up ( Amount, Colour, price )\n", "");
        Map<String, CompletionItem> items = byLabel(analyzer.completions(
                DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, withoutTheImport)));

        assertFalse(items.containsKey("Amount"), "the import is gone: " + items.keySet());
        assertTrue(items.containsKey("length"), "the import that is still written is not");
    }

    @Test
    void aDocumentTheWorkspaceNoLongerHoldsIsForgotten() {
        Analyzer analyzer = new Analyzer();
        analyzer.completions(DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, DOWN));
        analyzer.completions(UP_URI, new Position(2, 0), graphOf(UP_URI, UP));

        // down.sou is asked about again after the workspace stopped holding it: nothing of it is
        // remembered, so the answer is what a document this server has never seen would get.
        List<CompletionItem> items = analyzer.completions(
                DOWN_URI, IN_THE_BODY, graphOf(UP_URI, UP, DOWN_URI, broken(DOWN)));
        assertEquals(List.of(), fromElsewhere(items, "down"));
    }

    @Test
    void aBindingInForceShadowsAnImportOfTheSameSpelling() {
        String shadowing = DOWN.replace("let f (x) = x", "let f (length) = length");
        Analyzer analyzer = new Analyzer();
        Map<String, CompletionItem> items = byLabel(analyzer.completions(
                DOWN_URI, new Position(8, 20), graphOf(UP_URI, UP, DOWN_URI, shadowing)));

        assertEquals(CompletionItem.VARIABLE, items.get("length").kind(),
                "the param is what `length` means in this body, so it is what is offered");
        assertEquals(1, items.values().stream().filter(i -> i.label().equals("length")).count(),
                "and only once");
    }

    // --- a module written across two documents ---

    private static final String CRM = """
            module crm exposing ( Customer )

            data Customer = { id: Int }

            behavior g : (c: Customer) -> Int
            let g (c) = c.id
            """;

    private static final String CRM_ROWS = """
            examples for crm

            let someone = Customer { id = 1 }
            """;

    private static final String CRM_URI = "file:///crm.sou";
    private static final String ROWS_URI = "file:///crm.examples.sou";

    /** An attached file writes no import line, and its module's declarations are in scope bare. */
    @Test
    void anAttachedFileIsOfferedItsModulesDeclarations() {
        Analyzer analyzer = new Analyzer();
        Map<String, CompletionItem> items = byLabel(analyzer.completions(
                ROWS_URI, new Position(2, 30), graphOf(CRM_URI, CRM, ROWS_URI, CRM_ROWS)));

        assertEquals(new CompletionItem("Customer", CompletionItem.CLASS, "crm"),
                items.get("Customer"),
                "declared in the module's own source, reached bare here: " + items.keySet());
        assertTrue(items.containsKey("someone"), "and what this document itself declares");
    }

    /**
     * The module goes out of the compile when either of its documents will not parse, so the
     * partition has to be the document. A sibling's declarations are from elsewhere seen from here,
     * and are what is kept.
     */
    @Test
    void aSiblingsDeclarationsAreKeptWhileTheSiblingWillNotParse() {
        Analyzer analyzer = new Analyzer();
        analyzer.completions(ROWS_URI, new Position(2, 30), graphOf(CRM_URI, CRM, ROWS_URI, CRM_ROWS));

        String brokenCrm = CRM.replace("let g (c) = c.id", "let g (c) = ((((\nlet g (c) = c.id");
        Map<String, CompletionItem> items = byLabel(analyzer.completions(
                ROWS_URI, new Position(2, 30), graphOf(CRM_URI, brokenCrm, ROWS_URI, CRM_ROWS)));

        assertEquals("crm", items.get("Customer").detail(),
                "the sibling will not parse and its declarations are still offered here");
    }

    /**
     * The other direction, which is the case the per-document partition exists for: one answer holds
     * a sibling's remembered declarations and a declaration typed into this document since it
     * stopped parsing.
     */
    @Test
    void aDocumentThatWillNotParseOffersItsSiblingAndWhatIsBeingTypedInIt() {
        Analyzer analyzer = new Analyzer();
        analyzer.completions(ROWS_URI, new Position(2, 30), graphOf(CRM_URI, CRM, ROWS_URI, CRM_ROWS));

        String beingTyped = CRM_ROWS + "\nlet another = Customer { id = 2\nlet third = 3\n";
        Set<String> labels = byLabel(analyzer.completions(
                ROWS_URI, new Position(2, 30), graphOf(CRM_URI, CRM, ROWS_URI, beingTyped)))
                .keySet().stream().collect(Collectors.toSet());

        assertTrue(labels.contains("Customer"), "remembered from the sibling: " + labels);
        assertTrue(labels.contains("third"), "read off this document as it now is: " + labels);
    }
}
