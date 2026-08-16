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
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The declarations a document is owed go on being offered while the compiler cannot say what it
 * declares.
 *
 * <p>Which behaviors have no implementation is the compile's answer, and a document that will not
 * parse is held out of the compile — which is the document being typed in. Writing the first two
 * letters of {@code let} is enough to break it, so a list that could only answer from the current
 * compile would go empty at the keystroke that started the declaration it is there to offer.
 *
 * <p>What is offered is then the last answer the compiler gave about this document, and never a
 * blend of that and this one: written only where the compile answered, read only where it did not.
 * So a behavior deleted from a document that still parses stops being offered at once, and one
 * deleted while the document will not parse comes back to being offered until it parses again — the
 * compiler has said nothing about that document since, and this says what it last said rather than
 * guessing past it.
 */
class ADeclarationSurvivesTheKeystrokeThatBrokeTheFileTest {

    private static final String URI = "file:///m.sou";

    private static final String MODULE = """
            module m

            data MemberId = String

            behavior findMember : (id: MemberId) -> MemberId

            let place (id) = id
            """;

    /** The same document with a line no recovery makes into a module. */
    private static final String BROKEN = MODULE.replace("let place (id) = id",
            "let place (id) = ((((\nlet place (id) = id");

    @Test
    void aDeclarationOfferedWhileTheDocumentParsesIsStillOfferedWhenItDoesNot() {
        Analyzer analyzer = new Analyzer();
        assertNotNull(offered(analyzer, MODULE).get("let findMember"),
                "nothing was offered while the document parses");

        CompletionItem afterTheKeystroke = offered(analyzer, BROKEN).get("let findMember");
        assertNotNull(afterTheKeystroke, "the offer went away when the document stopped parsing");
        assertEquals("let findMember (id) = body\n", afterTheKeystroke.writes().text());
    }

    /** An analyzer that never saw the document parse offers the forms and nothing it did not read. */
    @Test
    void aDocumentThatNeverParsedIsOfferedNothingItDidNotRead() {
        Map<String, CompletionItem> items = offered(new Analyzer(), BROKEN);
        assertNull(items.get("let findMember"),
                "a signature nothing ever read was offered anyway");
        assertEquals("let name (param) = body\n", items.get("let").writes().text(),
                "the form itself is still offered, stating nothing it did not read");
    }

    /** What the compile can answer is taken from it, so a deletion that parses takes the offer away. */
    @Test
    void aBehaviorDeletedFromADocumentThatParsesStopsBeingOffered() {
        Analyzer analyzer = new Analyzer();
        offered(analyzer, MODULE);
        assertFalse(offered(analyzer, MODULE.replace(
                        "behavior findMember : (id: MemberId) -> MemberId\n", ""))
                        .containsKey("let findMember"),
                "a behavior that is no longer written was offered from what was remembered");
    }

    /**
     * A question the compiler did not answer is not an answer of nothing.
     *
     * <p>A document may parse and still leave the compiler unable to say what a behavior depends on
     * or what it takes. A row written from that would state no stand-in for what its target depends
     * on, which is E1908 the moment it is completed — so what those questions going unanswered
     * means is that nothing is answered here either, and the last answer that was given stands.
     *
     * <p>The module is made unanswerable by a composition that composes with itself, which is a
     * mistake reported where it is written and leaves what every behavior in the module requires
     * with no answer. The rows already offered are about behaviors that composition says nothing
     * about, and none of them stop needing what they needed.
     */
    @Test
    void aQuestionTheCompilerDidNotAnswerIsNotAnAnswerOfNothing() {
        Analyzer analyzer = new Analyzer();
        CompletionItem whole = offered(analyzer, DEPENDING).get("example place");
        assertNotNull(whole, "nothing offered a row while the compiler could answer");
        assertTrue(whole.writes().text().contains("with findMember = value"),
                "the row does not supply what nothing stands in for: " + whole.writes().text());

        CompletionItem afterTheCycle = offered(analyzer, DEPENDING + CYCLE).get("example place");
        assertNotNull(afterTheCycle,
                "the offer went away when a question about the module went unanswered");
        assertTrue(afterTheCycle.writes().text().contains("with findMember = value"),
                "a row was offered with nothing standing in for what it depends on: "
                        + afterTheCycle.writes().text());
    }

    private static final String DEPENDING = """
            module m

            data MemberId = String

            behavior findMember : (id: MemberId) -> MemberId

            behavior place : (id: MemberId) -> MemberId
                depends on findMember

            let place (id, findMember) = findMember(id)
            """;

    /** A composition that reaches itself: what this module requires has no answer while it stands. */
    private static final String CYCLE = "\nbehavior loop = loop >-> place\n";

    private static Map<String, CompletionItem> offered(Analyzer analyzer, String source) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(URI, source);
        int line = (int) source.lines().count();
        List<CompletionItem> items = analyzer.completions(URI, new Position(line, 0),
                ModuleGraph.of(sources));
        Map<String, CompletionItem> byLabel = new LinkedHashMap<>();
        for (CompletionItem item : items) {
            byLabel.put(item.label(), item);
        }
        return byLabel;
    }
}
