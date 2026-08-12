package souther.lsp.analysis;

import souther.compiler.cst.CstLexer;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The semantic-token classifier must know every reserved word, so an editor colours a keyword added
 * to or renamed in the lexer without a second list being kept in step by hand. The TextMate grammar
 * has this guard already ({@code TmLanguageGeneratorTest}); this is the same guard for the language
 * server, which classifies by node kind rather than by text and so has its own list to forget.
 */
class EveryKeywordIsHighlightedTest {

    private static final int KEYWORD = Analyzer.TOKEN_TYPES.indexOf("keyword");
    private static final int PROPERTY = Analyzer.TOKEN_TYPES.indexOf("property");

    @Test
    void everyReservedWordIsClassifiedAsAKeyword() {
        List<String> keywords = new ArrayList<>(CstLexer.keywords());
        String source = "module demo\n" + String.join(" ", keywords) + "\n";

        List<String> notKeywords = new ArrayList<>();
        for (String keyword : keywords) {
            if (!typesOf(source, keyword).contains(KEYWORD)) {
                notKeywords.add(keyword);
            }
        }
        assertEquals(List.of(), notKeywords,
                "Analyzer.isKeyword must name every kind in CstLexer.keywords()");
    }

    /**
     * {@code on} is not reserved — it is read as the second word of {@code depends on} — so the guard
     * above cannot reach it. It is coloured from its position instead, which is also what keeps a
     * field named {@code on} an ordinary field.
     */
    @Test
    void theOnOfDependsOnIsAKeywordAndAFieldNamedOnIsNot() {
        String source = """
                module demo
                data In = { on: Int }
                data Out = { n: Int }
                behavior clock : () -> Out constructs Out
                behavior use : (i: In) -> Out
                    depends on clock
                let use (i, clock) = clock()
                """;

        assertEquals(List.of(PROPERTY, KEYWORD), typesOf(source, "on"),
                "the field named `on` stays a field; the `on` of `depends on` is the keyword");
    }

    /** The semantic-token types of every token spelled {@code text}, in source order. */
    private List<Integer> typesOf(String source, String text) {
        String[] lines = source.split("\n", -1);
        int[] data = new Analyzer().semanticTokens(source);
        List<Integer> out = new ArrayList<>();
        int line = 0;
        int character = 0;
        for (int i = 0; i < data.length; i += 5) {
            line += data[i];
            character = data[i] == 0 ? character + data[i + 1] : data[i + 1];
            int length = data[i + 2];
            if (lines[line].regionMatches(character, text, 0, length) && length == text.length()) {
                out.add(data[i + 3]);
            }
        }
        return out;
    }
}
