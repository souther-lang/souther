package souther.compiler.highlight;

import souther.compiler.cst.CstLexer;
import souther.compiler.cst.SyntaxKind;
import org.junit.jupiter.api.Test;
import tools.jackson.databind.json.JsonMapper;

import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** The generated TextMate grammar is valid JSON, categorises every lexer keyword, accounts for every
 * symbol the kinds spell, and matches the committed grammar file — so a form added to or dropped from
 * the language forces the highlighter to be regenerated. */
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
     * The symbols the grammar paints and the ones it leaves alone are exactly the symbols the
     * language writes, and no symbol is in both.
     *
     * <p>The editor's classification is its own — {@code ...}, {@code =} and {@code ?} are painted
     * here and called delimiters by the specification's inventory — so this cannot ask the two sides
     * to agree on which symbol is an operator. What it can ask is that neither side hold a symbol the
     * other has never heard of. A form dropped from the language and left in the list below goes on
     * being painted in an editor after the compiler has stopped reading it, and nothing else in the
     * build would say so.
     *
     * <p>Written as a partition rather than as a covering: a covering alone passes when a bracket is
     * mistakenly listed as an operator, because the union does not change.
     */
    @Test
    void everySymbolTheLanguageWritesIsPaintedOrDeliberatelyNot() {
        Set<String> painted = new TreeSet<>(TmLanguageGenerator.OPERATORS);

        Set<String> both = new TreeSet<>(painted);
        both.retainAll(NOT_PAINTED);
        assertEquals(Set.of(), both,
                "a symbol cannot be an operator and punctuation the grammar leaves alone");

        Set<String> classified = new TreeSet<>(painted);
        classified.addAll(NOT_PAINTED);
        assertEquals(symbolsTheKindsSpell(), classified,
                "the grammar and the kinds disagree about which symbols the language writes");
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

    /** The punctuation the grammar deliberately does not paint. */
    private static final Set<String> NOT_PAINTED =
            Set.of("(", ")", "{", "}", "[", "]", ",", ".", ":");

    /** Every symbol the language writes: the spelling of each kind that spells itself, less the
     *  words. A keyword spells itself too and is categorised by its own rule above. */
    private static Set<String> symbolsTheKindsSpell() {
        Set<String> words = Set.copyOf(CstLexer.keywords());
        Set<String> symbols = new TreeSet<>();
        for (SyntaxKind kind : SyntaxKind.values()) {
            kind.fixedSpelling().filter(spelled -> !words.contains(spelled)).ifPresent(symbols::add);
        }
        return symbols;
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
