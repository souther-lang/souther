package souther.lsp.analysis;

import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.Position;
import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a declaration may be written, an editor is offered the declaration and not only the word it
 * starts with.
 *
 * <p>What may be written is the grammar's, and where in a file each of those may stand is the same
 * answer: a header opens a file, an import follows it, and everything else is a body item. An
 * {@code import} offered after the first definition would be an offer to write a syntax error.
 *
 * <p>Where a behavior can be read, what is offered for it is what it said. The parameters of the
 * {@code let} that implements it are the behavior's, and a row for it takes as many arguments as it
 * has inputs and supplies what nothing else stands in for. A behavior that already has an
 * implementation is not offered a second one.
 */
class ADeclarationIsOfferedWhereOneMayBeWrittenTest {

    private static final String URI = "file:///m.sou";

    private static final String MODULE = """
            module m

            data MemberId = String
            data Found = { id: MemberId }
            data Missing = { why: String }

            behavior findMember : (id: MemberId) -> Found | Missing

            behavior place : (id: MemberId) -> Found | Missing
                depends on findMember

            let place (id, findMember) = findMember(id)
            """;

    @Test
    void aBehaviorWithNoImplementationIsOfferedTheOneItsSignatureDescribes() {
        Map<String, CompletionItem> items = atEndOfFile();

        CompletionItem offered = items.get("let findMember");
        assertNotNull(offered, "nothing offers to implement findMember: " + items.keySet());
        assertEquals("let findMember (id) = body\n", offered.writes().text());
        assertEquals(CompletionItem.SNIPPET, offered.kind());
        assertEquals("m", offered.detail());
    }

    /** A behavior that has one is not offered another, which would be declaring its name twice. */
    @Test
    void aBehaviorThatHasAnImplementationIsNotOfferedAnother() {
        assertFalse(atEndOfFile().containsKey("let place"),
                "an implementation was offered for a behavior that has one");
    }

    /**
     * A row states the inputs and supplies what nothing stands in for.
     *
     * <p>{@code place} depends on {@code findMember} and nothing in this module fakes it, so a row
     * written without a stand-in could not run — which is E1908, reported the moment the row is
     * completed.
     */
    @Test
    void aRowSuppliesWhatNothingElseStandsInFor() {
        CompletionItem offered = atEndOfFile().get("example place");
        assertNotNull(offered, "nothing offers to write a row for place");
        assertTrue(offered.writes().text().contains("with findMember = value"),
                "the row does not supply findMember: " + offered.writes().text());
    }

    /** With no signature to read, the form is still offered — stating no parameters it did not read. */
    @Test
    void aFormIsOfferedWithNothingItDidNotRead() {
        Map<String, CompletionItem> items = atEndOfFile();
        assertEquals("let name (param) = body\n", items.get("let").writes().text());
        assertEquals(CompletionItem.SNIPPET, items.get("let").kind());
        assertNotNull(items.get("example"), "`example` is not a keyword and was never offered");
        assertNotNull(items.get("fake"), "`fake` is not a keyword and was never offered");
    }

    /** Inside a definition no declaration is offered, and the words are words again. */
    @Test
    void insideADefinitionTheWordsAreOfferedAndNotTheDeclarations() {
        Map<String, CompletionItem> items = at(lineOf("let place (id, findMember)"), 30);
        assertEquals(CompletionItem.KEYWORD, items.get("let").kind(),
                "a declaration was offered inside a definition");
        assertNull(items.get("let").writes(), "a keyword writes what it says");
        assertFalse(items.containsKey("let findMember"),
                "an implementation was offered from inside another definition");
    }

    /**
     * An import may follow the header, and may not follow a definition.
     *
     * <p>Both are the same fact about where the form stands, read from the catalog rather than from
     * a list kept here.
     *
     * <p>The word is still offered in both places. Which words may be written where is not something
     * this list answers — every keyword is offered at every position, as {@code then} and {@code
     * else} are at the top level — and nothing here made it answer it. What is offered where is the
     * declaration.
     */
    @Test
    void anImportIsOfferedWhereOneMayStand() {
        CompletionItem afterTheHeader = at(lineOf("module m") + 1, 0).get("import");
        assertNotNull(afterTheHeader.writes(),
                "an import declaration was not offered where one may be written");
        assertEquals(CompletionItem.SNIPPET, afterTheHeader.kind());
        assertNull(atEndOfFile().get("import").writes(),
                "an import was offered after a definition, where it will not parse");
    }

    private static Map<String, CompletionItem> atEndOfFile() {
        return at((int) MODULE.lines().count(), 0);
    }

    private static Map<String, CompletionItem> at(int line, int character) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(URI, MODULE);
        List<CompletionItem> items = new Analyzer()
                .completions(URI, new Position(line, character), ModuleGraph.of(sources));
        Map<String, CompletionItem> byLabel = new LinkedHashMap<>();
        for (CompletionItem item : items) {
            byLabel.put(item.label(), item);
        }
        return byLabel;
    }

    /** The line {@code marker} is written on. */
    private static int lineOf(String marker) {
        List<String> lines = MODULE.lines().toList();
        for (int i = 0; i < lines.size(); i++) {
            if (lines.get(i).startsWith(marker)) {
                return i;
            }
        }
        throw new IllegalArgumentException("no line starts with " + marker);
    }
}
