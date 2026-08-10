package souther.lsp.analysis;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;
import souther.compiler.editor.EditorSymbols;
import org.junit.jupiter.api.Test;

import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Every symbol the editor's classification paints arrives at a reader as an operator token.
 *
 * <p>Reading the classification is not the same as emitting from it. The classifier runs inside a
 * walk that drops tokens for reasons of its own — a token that spans lines, a node it does not
 * descend into — so a set comparison against {@link EditorSymbols} would hold while a symbol never
 * reached the client. This runs a program through {@link Analyzer#semanticTokens} and asks what came
 * out.
 *
 * <p>The fixture has to write every classified symbol, and the first assertion is what says so: a
 * symbol added to the classification with nothing exercising it fails here rather than being
 * silently untested.
 */
class EverySymbolTheEditorPaintsArrivesAsASemanticTokenTest {

    private static final String FIXTURE = "every-operator.sou";
    private static final int OPERATOR = Analyzer.TOKEN_TYPES.indexOf("operator");

    @Test
    void theFixtureWritesEverySymbolTheClassificationPaints() {
        Set<String> written = new TreeSet<>();
        for (SyntaxToken token : tokensOf(source())) {
            if (EditorSymbols.isOperator(token.kind())) {
                written.add(token.kind().fixedSpelling().orElseThrow());
            }
        }
        assertEquals(spellingsOf(EditorSymbols.operators()), written,
                "add a use of each missing symbol to " + FIXTURE);
    }

    /** A fixture that stops parsing stops writing the symbols it was written to write, and every
     *  assertion here would go on passing on what was left. */
    @Test
    void theFixtureParsesWithoutError() {
        assertEquals(List.of(), CstParser.parse(source()).errors());
    }

    @Test
    void everyOccurrenceOfAPaintedSymbolIsEmittedAsAnOperator() {
        String source = source();
        Map<Integer, Integer> emitted = emittedTypesByOffset(source);

        List<String> missed = new ArrayList<>();
        for (SyntaxToken token : tokensOf(source)) {
            if (!EditorSymbols.isOperator(token.kind())) {
                continue;
            }
            Integer type = emitted.get(token.start());
            if (type == null || type != OPERATOR) {
                missed.add(token.kind().fixedSpelling().orElseThrow() + " at " + token.start());
            }
        }
        assertEquals(List.of(), missed, "these are classified as operators and not emitted as one");
    }

    /** The other side of the classification: what it leaves alone reaches the reader uncoloured, so
     *  a client with no grammar under it sees the brackets and separators as text. */
    @Test
    void noPunctuationIsEmittedAsAnOperator() {
        String source = source();
        Map<Integer, Integer> emitted = emittedTypesByOffset(source);

        List<String> painted = new ArrayList<>();
        for (SyntaxToken token : tokensOf(source)) {
            if (!EditorSymbols.punctuation().contains(token.kind())) {
                continue;
            }
            if (emitted.containsKey(token.start())) {
                painted.add(token.kind().fixedSpelling().orElseThrow() + " at " + token.start());
            }
        }
        assertEquals(List.of(), painted, "these are left alone by the classification and painted");
    }

    /** The token type emitted at each source offset, decoded from the delta-encoded array the
     *  server sends. */
    private static Map<Integer, Integer> emittedTypesByOffset(String source) {
        List<Integer> lineStarts = new ArrayList<>();
        lineStarts.add(0);
        for (int i = 0; i < source.length(); i++) {
            if (source.charAt(i) == '\n') {
                lineStarts.add(i + 1);
            }
        }

        Map<Integer, Integer> byOffset = new HashMap<>();
        int[] data = new Analyzer().semanticTokens(source);
        int line = 0;
        int character = 0;
        for (int i = 0; i < data.length; i += 5) {
            line += data[i];
            character = data[i] == 0 ? character + data[i + 1] : data[i + 1];
            byOffset.put(lineStarts.get(line) + character, data[i + 3]);
        }
        return byOffset;
    }

    private static Set<String> spellingsOf(Set<SyntaxKind> kinds) {
        Set<String> spellings = new TreeSet<>();
        for (SyntaxKind kind : kinds) {
            spellings.add(kind.fixedSpelling().orElseThrow());
        }
        return spellings;
    }

    private static List<SyntaxToken> tokensOf(String source) {
        List<SyntaxToken> tokens = new ArrayList<>();
        collect(CstParser.parse(source).root(), tokens);
        return tokens;
    }

    private static void collect(SyntaxNode node, List<SyntaxToken> out) {
        for (SyntaxElement element : node.children()) {
            if (element instanceof SyntaxNode child) {
                collect(child, out);
            } else {
                out.add((SyntaxToken) element);
            }
        }
    }

    private static String source() {
        try (InputStream in = EverySymbolTheEditorPaintsArrivesAsASemanticTokenTest.class
                .getResourceAsStream(FIXTURE)) {
            assertNotNull(in, FIXTURE + " is missing from the test resources");
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (Exception e) {
            throw new IllegalStateException("could not read " + FIXTURE, e);
        }
    }
}
