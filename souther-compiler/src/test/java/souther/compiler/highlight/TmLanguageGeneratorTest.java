package souther.compiler.highlight;

import souther.compiler.cst.CstLexer;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.editor.EditorSymbols;
import org.junit.jupiter.api.Test;
import tools.jackson.databind.json.JsonMapper;

import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** The generated TextMate grammar is valid JSON, categorises every lexer keyword, paints the symbols
 * the editor's classification names, and matches the committed grammar file — so a form added to or
 * dropped from the language forces the highlighter to be regenerated. */
class TmLanguageGeneratorTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    @SuppressWarnings("unchecked")
    void theGrammarIsValidJsonForSourceSouther() {
        Map<String, Object> grammar = (Map<String, Object>) JSON.readValue(
                TmLanguageGenerator.generate(), Object.class);
        assertEquals("source.souther", grammar.get("scopeName"));
        assertTrue(grammar.containsKey("repository"));
    }

    @Test
    void everyLexerKeywordIsCategorised() {
        Set<String> inGrammar = new TreeSet<>();
        inGrammar.addAll(alternatives("declaration-keywords"));
        inGrammar.addAll(alternatives("control-keywords"));
        inGrammar.addAll(alternatives("booleans"));
        assertEquals(new TreeSet<>(CstLexer.keywords()), inGrammar,
                "the highlighter grammar must categorise exactly the lexer's keywords");
    }

    /**
     * The grammar paints every symbol {@link EditorSymbols} classifies as an operator, whole, and
     * none of the punctuation it leaves alone.
     *
     * <p>Run as a regex against each symbol rather than compared as a set of strings. Between the
     * classification and what an editor colours are an escaping and an ordering, and both fail in
     * ways a set comparison cannot see: an unescaped {@code |} paints nothing it was meant to, and a
     * short form listed before a longer one paints the first character of it and leaves the rest.
     */
    @Test
    void theGrammarPaintsEveryClassifiedOperatorWholeAndNoPunctuation() {
        Pattern operators = Pattern.compile(operatorPattern());

        Set<String> notPaintedWhole = new TreeSet<>();
        for (SyntaxKind kind : EditorSymbols.operators()) {
            String spelled = kind.fixedSpelling().orElseThrow();
            Matcher m = operators.matcher(spelled);
            if (!m.find() || m.start() != 0 || m.end() != spelled.length()) {
                notPaintedWhole.add(spelled);
            }
        }
        assertEquals(Set.of(), notPaintedWhole,
                "the grammar does not paint these as operators, or paints only part of them");

        Set<String> painted = new TreeSet<>();
        for (SyntaxKind kind : EditorSymbols.punctuation()) {
            String spelled = kind.fixedSpelling().orElseThrow();
            if (operators.matcher(spelled).find()) {
                painted.add(spelled);
            }
        }
        assertEquals(Set.of(), painted,
                "the grammar paints punctuation the classification leaves alone");
    }

    /** A spelling appears once, and a longer form is listed before any prefix of it, so the
     *  alternation cannot match the prefix and leave the rest of the symbol unpainted. */
    @Test
    void theAlternationIsOrderedAndWithoutRepeats() {
        assertEquals(TmLanguageGenerator.OPERATORS.size(),
                Set.copyOf(TmLanguageGenerator.OPERATORS).size(),
                "an operator is listed more than once: " + TmLanguageGenerator.OPERATORS);
        for (int i = 0; i < TmLanguageGenerator.OPERATORS.size(); i++) {
            String longer = TmLanguageGenerator.OPERATORS.get(i);
            for (int j = 0; j < i; j++) {
                String earlier = TmLanguageGenerator.OPERATORS.get(j);
                assertEquals(false, longer.startsWith(earlier),
                        "`" + earlier + "` is listed before `" + longer + "`, which begins with it");
            }
        }
    }

    @Test
    void theCommittedGrammarMatchesTheGenerator() throws Exception {
        String committed;
        try (InputStream in = TmLanguageGenerator.class.getResourceAsStream(
                TmLanguageGenerator.RESOURCE)) {
            assertNotNull(in, "run TmLanguageGenerator to write " + TmLanguageGenerator.COMMITTED);
            committed = new String(in.readAllBytes(), StandardCharsets.UTF_8);
        }
        assertEquals(TmLanguageGenerator.generate(), committed,
                "the committed grammar is stale — regenerate it with TmLanguageGenerator");
    }

    /** The regex the grammar matches operators with. */
    @SuppressWarnings("unchecked")
    private String operatorPattern() {
        Map<String, Object> grammar = (Map<String, Object>) JSON.readValue(
                TmLanguageGenerator.generate(), Object.class);
        Map<String, Object> repository = (Map<String, Object>) grammar.get("repository");
        Map<String, Object> node = (Map<String, Object>) repository.get("operators");
        return (String) node.get("match");
    }

    /** The keyword alternatives of a repository entry whose match is {@code \b(a|b|c)\b}. */
    @SuppressWarnings("unchecked")
    private Set<String> alternatives(String entry) {
        Map<String, Object> grammar = (Map<String, Object>) JSON.readValue(
                TmLanguageGenerator.generate(), Object.class);
        Map<String, Object> repository = (Map<String, Object>) grammar.get("repository");
        Map<String, Object> node = (Map<String, Object>) repository.get(entry);
        String match = (String) node.get("match");
        String group = match.substring(match.indexOf('(') + 1, match.lastIndexOf(')'));
        return new TreeSet<>(Set.of(group.split("\\|")));
    }
}
