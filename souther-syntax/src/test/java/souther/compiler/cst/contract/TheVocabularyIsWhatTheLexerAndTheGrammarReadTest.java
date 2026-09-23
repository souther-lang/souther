package souther.compiler.cst.contract;

import souther.compiler.cst.ContextualWord;
import souther.compiler.cst.CstLexer;
import souther.compiler.cst.IdentifierAlphabet;
import souther.compiler.cst.SyntaxKind;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code syntax/vocabulary.json} lists the words and symbols the lexer reads and the grammar
 * writes, and each list is held to the set that decides it here.
 *
 * <p>The vocabulary is not written from the compiler. It is the contract's own list, written for
 * a tool that reads no Java, and the compiler's sets are compared with it: the reserved words with
 * the ones the lexer reserves, the contextual words with {@link ContextualWord}, the fixed spellings
 * with what each {@link SyntaxKind} spells. The grammar is compared with it too — every terminal a
 * production outside the lexical grammar writes is a fixed spelling or a contextual word, and every
 * one of those is written somewhere — so a symbol the parser reads and no production mentions, or
 * the other way round, is found here.
 */
class TheVocabularyIsWhatTheLexerAndTheGrammarReadTest {

    private static final JsonNode VOCABULARY =
            JsonMapper.builder().build().readTree(SyntaxContract.text("vocabulary.json"));

    private static final Grammar GRAMMAR = SyntaxContract.grammar();

    @Test
    void theFixedSpellingsAreTheOnesTheKindsSpell() {
        Set<String> spelled = new TreeSet<>();
        for (SyntaxKind kind : SyntaxKind.values()) {
            kind.fixedSpelling().ifPresent(spelled::add);
        }
        assertEquals(spelled, new TreeSet<>(listed("fixedSpellings")));
    }

    @Test
    void theReservedWordsAreTheOnesTheLexerReservesAndSpellThemselves() {
        assertEquals(new TreeSet<>(CstLexer.keywords()), new TreeSet<>(listed("reservedWords")));
        assertTrue(listed("fixedSpellings").containsAll(listed("reservedWords")),
                "a reserved word is a fixed spelling");
    }

    @Test
    void theContextualWordsAreTheOnesTheParserReadsAsKeywords() {
        Set<String> words = new TreeSet<>();
        for (ContextualWord word : ContextualWord.values()) {
            words.add(word.spelling());
        }
        assertEquals(words, new TreeSet<>(listed("contextualWords")));
    }

    @Test
    void theStructuralGrammarWritesExactlyTheFixedSpellingsAndTheContextualWords() {
        Set<String> vocabulary = new TreeSet<>(listed("fixedSpellings"));
        vocabulary.addAll(listed("contextualWords"));
        assertEquals(vocabulary, new TreeSet<>(GRAMMAR.structuralTerminals()));
    }

    /**
     * The token classes are what the grammar's head says they are: the open token classes are
     * lexical productions, the structural grammar reads the lexical grammar through them and
     * through nothing else, and the ones it never reads are the trivia. A lexical production the
     * structure named that is not a token class would be a part of a token read as a token.
     */
    @Test
    void theStructureReadsTheLexicalGrammarOnlyThroughTheTokenClasses() {
        assertTrue(GRAMMAR.lexical().containsAll(listed("openTokens")),
                "open tokens the lexical grammar does not define");
        assertTrue(listed("openTokens").containsAll(listed("trivia")), "trivia that is no token class");
        Set<String> read = new TreeSet<>(listed("openTokens"));
        read.removeAll(listed("trivia"));
        assertEquals(read, new TreeSet<>(GRAMMAR.lexicalNamedByTheStructure()));
    }

    /**
     * The Unicode version is one value, said three times: by the vocabulary, by every property the
     * grammar names, and by the table the lexer reads names with. A property named without its
     * version is refused as well, since it would be read in whichever version its reader has.
     */
    @Test
    void everyUnicodePropertyIsReadInTheVersionTheAlphabetIsSpelledFrom() {
        String version = VOCABULARY.get("unicodeVersion").asString();
        assertEquals(IdentifierAlphabet.unicodeVersion(), version);
        List<String> named = new ArrayList<>();
        for (Grammar.Special each : GRAMMAR.specials()) {
            if (each.text().contains("XID_") || each.text().contains("Unicode")) {
                Matcher written = UNICODE_VERSION.matcher(each.text());
                named.add(written.find() ? written.group(1) : "no version: " + each.text());
            }
        }
        assertFalse(named.isEmpty(), "the grammar names no Unicode property");
        assertEquals(List.of(version), named.stream().distinct().toList());
    }

    private static final Pattern UNICODE_VERSION = Pattern.compile("Unicode (\\d+\\.\\d+\\.\\d+)");

    @Test
    void theFormatIsTheOneThisReads() {
        assertEquals(1, VOCABULARY.get("formatVersion").asInt());
    }

    /** One list of the vocabulary, refused where it names an entry twice. */
    private static List<String> listed(String field) {
        JsonNode node = VOCABULARY.get(field);
        assertTrue(node != null && node.isArray(), "the vocabulary has no list " + field);
        List<String> out = new ArrayList<>();
        Set<String> seen = new HashSet<>();
        for (JsonNode entry : node) {
            String written = entry.asString();
            assertTrue(seen.add(written), field + " lists " + written + " twice");
            out.add(written);
        }
        return out;
    }
}
