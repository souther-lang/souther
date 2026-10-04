package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;
import souther.lsp.protocol.WorkspaceSymbol;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One text is parsed once, however many questions are asked of it and however many places in it a
 * question needs — and only a document the editor has open keeps the tree that parse made.
 *
 * <p>Every request arrives with the whole workspace, and every one of them needs some document as a
 * tree or as lines and columns. A question that parsed for itself would pay for the document on
 * every request, and one that parsed for each place it needed — a hint for each parameter, a
 * location for each use — once per answer it gave. So the parse is kept with the text it was made
 * of, and what is counted here is how many times a document was parsed, which stays where it is
 * until a text changes.
 *
 * <p>A file the editor has closed keeps the small facts about it and not its tree, because every
 * file of the workspace has a reading and a tree is many times its text. What the editor asks of a
 * closed file — its outline, where a use of a name in it is — is answered without reading it again;
 * the places come from the workspace compile, which has laid out every file it holds.
 *
 * <p>That every parse goes through the one that is counted is held elsewhere, over the compiled
 * classes: a question that parsed beside it would leave this count where it is.
 */
class ADocumentIsParsedOnceForEveryQuestionAskedOfItTest {

    private static final String LIB_URI = "file:///lib.sou";

    private static final String MODEL_URI = "file:///m.sou";

    private static final String LIB = """
            module lib exposing ( Cost, priced )

            data Cost = { amount: Int }

            behavior priced : (c: Cost) -> Int
            let priced (c) = c.amount
            """;

    private static final String MODEL = """
            module m

            import lib as l ( Cost )

            behavior submit : (c: Cost) -> Int
            let submit (c) = c.amount

            behavior both : (first: Cost, second: Cost) -> Int
            let both (first, second) = first.amount + second.amount
            """;

    /** On the {@code Cost} the first signature names. */
    private static final Position ON_COST = new Position(4, 22);

    /** On the {@code c} the first body reads. */
    private static final Position ON_C = new Position(5, 17);

    @Test
    void aDiagnoseParsesEachTextItHasNotParsedAlready() {
        Analyzer analyzer = new Analyzer();

        analyzer.diagnostics(workspace(MODEL));
        assertEquals(2, analyzer.parsesMade(), "two documents, each parsed once");

        analyzer.diagnostics(workspace(MODEL));
        assertEquals(2, analyzer.parsesMade(),
                "nothing was edited, so there is nothing to parse again");

        analyzer.diagnostics(workspace(MODEL.replace("c.amount", "c.amount + 1")));
        assertEquals(3, analyzer.parsesMade(), "one document was edited, and only it is parsed");
    }

    @Test
    void noQuestionAskedAfterTheDiagnoseParsesAnyDocumentAgain() {
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(workspace(MODEL));
        int parsed = analyzer.parsesMade();

        for (Map.Entry<String, Consumer<ModuleGraph>> question : questions(analyzer).entrySet()) {
            // A graph of its own for each, the way a server builds one for each request.
            question.getValue().accept(workspace(MODEL));
            assertEquals(parsed, analyzer.parsesMade(),
                    question.getKey() + " parsed a document the diagnose had already read");
        }
    }

    /**
     * And with the library closed, which is the file every question here reaches into: its
     * declarations are what the model's names resolve to, and its outline is half of what a
     * workspace symbol search answers with.
     */
    @Test
    void aClosedFileIsAnsweredForWithoutBeingParsedAgain() {
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(withTheLibraryClosed());
        int parsed = analyzer.parsesMade();

        Map<String, Consumer<ModuleGraph>> questions = questions(analyzer);
        // A rename writes into the files it renames in, and reads each of them, open or closed, to
        // find out what to write: the tree a closed file let go is read again for it, once.
        questions.remove("rename");
        for (Map.Entry<String, Consumer<ModuleGraph>> question : questions.entrySet()) {
            question.getValue().accept(withTheLibraryClosed());
            assertEquals(parsed, analyzer.parsesMade(),
                    question.getKey() + " parsed the closed library again");
        }
        Set<String> declared = analyzer.workspaceSymbols("", withTheLibraryClosed()).stream()
                .filter(symbol -> symbol.location().uri().equals(LIB_URI))
                .map(WorkspaceSymbol::name).collect(Collectors.toSet());
        assertEquals(Set.of("Cost", "priced"), declared,
                "and what it declares is still found, from the outline its reading kept");
    }

    @Test
    void onlyAnOpenDocumentKeepsItsTree() {
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(withTheLibraryClosed());

        assertFalse(analyzer.holdsATreeOf(LIB_URI), "the library is closed");
        assertTrue(analyzer.holdsATreeOf(MODEL_URI), "the model is open");
    }

    /**
     * The same text, opened and closed again. The tree goes with the document and not with the
     * text: opening it has to parse it, because the tree was let go, and closing it lets the tree go
     * without reading anything.
     */
    @Test
    void openingAClosedFileReadsItAndClosingItLetsTheTreeGo() {
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(withTheLibraryClosed());
        int parsed = analyzer.parsesMade();

        analyzer.diagnostics(workspace(MODEL));
        assertTrue(analyzer.holdsATreeOf(LIB_URI), "opened, the library has a tree again");
        assertEquals(parsed + 1, analyzer.parsesMade(), "which it was read again for");

        analyzer.diagnostics(withTheLibraryClosed());
        assertFalse(analyzer.holdsATreeOf(LIB_URI), "closed again, it lets the tree go");
        assertEquals(parsed + 1, analyzer.parsesMade(), "without being read for that");
    }

    private static Map<String, Consumer<ModuleGraph>> questions(Analyzer analyzer) {
        Map<String, Consumer<ModuleGraph>> questions = new LinkedHashMap<>();
        questions.put("inlay hints", graph -> analyzer.inlayHints(MODEL_URI, null, graph));
        questions.put("references", graph -> analyzer.references(MODEL_URI, ON_COST, graph, true));
        questions.put("references of a local",
                graph -> analyzer.references(MODEL_URI, ON_C, graph, false));
        questions.put("highlights", graph -> analyzer.documentHighlights(MODEL_URI, ON_C, graph));
        questions.put("hover", graph -> analyzer.hover(MODEL_URI, MODEL, ON_COST, graph));
        questions.put("definition", graph -> analyzer.definition(MODEL_URI, ON_COST, graph));
        questions.put("completion", graph -> analyzer.completions(MODEL_URI, ON_C, graph));
        questions.put("signature help", graph -> analyzer.signatureHelp(MODEL_URI, ON_C, graph));
        questions.put("selection ranges",
                graph -> analyzer.selectionRanges(MODEL_URI, ON_C, graph));
        questions.put("rename", graph -> analyzer.renameEdits(MODEL_URI, ON_COST, graph, "Price"));
        questions.put("code actions", graph -> analyzer.codeActions(MODEL_URI, MODEL,
                new Range(ON_C, ON_C), graph));
        questions.put("code lenses", graph -> analyzer.codeLenses(MODEL_URI, graph));
        questions.put("workspace symbols", graph -> analyzer.workspaceSymbols("", graph));
        questions.put("document symbols", graph -> analyzer.documentSymbols(MODEL_URI, MODEL));
        questions.put("semantic tokens", graph -> analyzer.semanticTokens(MODEL_URI, MODEL));
        return questions;
    }

    private static ModuleGraph workspace(String model) {
        return ModuleGraph.of(sources(model));
    }

    private static ModuleGraph withTheLibraryClosed() {
        return ModuleGraph.of(sources(MODEL), ModulesOnThePath.NONE, Set.of(MODEL_URI));
    }

    private static Map<String, String> sources(String model) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(LIB_URI, LIB);
        sources.put(MODEL_URI, model);
        return sources;
    }
}
