package souther.compiler.highlight;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.cst.CstLexer;
import souther.compiler.cst.GreenToken;
import souther.compiler.cst.IdentifierAlphabet;
import souther.compiler.cst.SyntaxKind;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The editor grammar admits the names the compiler admits.
 *
 * <p>Held by writing the same text to both and comparing what each makes of it, not by reading one
 * pattern against the other: the grammar is a regular expression and the compiler is a scan, and two
 * spellings of one rule agree only where something writes to both. What the grammar colours a type
 * variable is what the lexer makes a {@code TYPEVAR} of, and nothing else — the arrangement before
 * this had the grammar carrying an ASCII pattern of its own, so the compiler read {@code 'あ} and the
 * editor left it uncoloured.
 */
class AnEditorReadsTheNamesTheCompilerReadsTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** Every way a `'` may be followed, written as an author would write it. */
    private static final List<String> WRITTEN = List.of(
            "'a", "'b2", "'foo_bar", "'A", "'z9",
            "'あ", "'数量", "'Έ", "'₻7",          // a name outside the basic plane
            "'_a", "'_", "'$x", "'1", "'", "''", "'-", "' a", "'·");

    @Test
    void theGrammarColoursAsATypeVariableWhatTheLexerMakesOne() {
        Pattern grammar = Pattern.compile(matchOf("type-variable"));
        List<String> disagreed = new ArrayList<>();
        for (String written : WRITTEN) {
            Matcher m = grammar.matcher(written);
            boolean coloured = m.lookingAt() && m.end() == written.length();
            if (coloured != isOneTypeVariable(written)) {
                disagreed.add(written + (coloured
                        ? " is coloured a type variable and is not one"
                        : " is a type variable and is not coloured one"));
            }
        }
        assertEquals(List.of(), disagreed, "the editor and the compiler read different names");
    }

    /**
     * And at every edge of the alphabet, which is where a class written out can differ from the
     * answer it was written from.
     *
     * <p>Both sides are ranges, so they agree everywhere if they agree at each range's first and
     * last character and at the character on either side of it: a difference anywhere else would
     * have to be a range one of them holds and the other does not, and that range has edges of its
     * own. The edges are found by asking the alphabet, so a range added later brings its own.
     */
    @Test
    void andTheyAgreeAtEveryEdgeOfIt() {
        Pattern start = Pattern.compile("[" + IdentifierAlphabet.startClass() + "]");
        Pattern carriesOn = Pattern.compile("[" + IdentifierAlphabet.continueClass() + "]");
        List<Integer> edges = edges();
        assertTrue(edges.size() > 3000,
                "the alphabet is ranges over the whole of Unicode, not a handful: " + edges.size());
        for (int codePoint : edges) {
            String written = new String(Character.toChars(codePoint));
            assertEquals(IdentifierAlphabet.isStart(codePoint), start.matcher(written).matches(),
                    () -> "a name begins with " + written + " in one of them and not the other");
            assertEquals(IdentifierAlphabet.isContinue(codePoint),
                    carriesOn.matcher(written).matches(),
                    () -> "a name carries on with " + written + " in one of them and not the other");
        }
    }

    /** Every code point at which either answer changes, and its neighbour on each side. */
    private static List<Integer> edges() {
        List<Integer> out = new ArrayList<>();
        boolean previousStart = false;
        boolean previousContinue = false;
        for (int codePoint = 0; codePoint <= Character.MAX_CODE_POINT; codePoint++) {
            boolean begins = IdentifierAlphabet.isStart(codePoint);
            boolean carriesOn = IdentifierAlphabet.isContinue(codePoint);
            if (begins != previousStart || carriesOn != previousContinue) {
                if (codePoint > 0) {
                    out.add(codePoint - 1);
                }
                out.add(codePoint);
            }
            previousStart = begins;
            previousContinue = carriesOn;
        }
        return out;
    }

    /** Whether the compiler reads {@code written} as one type variable and nothing else. */
    private static boolean isOneTypeVariable(String written) {
        CstLexer.Result lexed = CstLexer.lex(written);
        List<GreenToken> code = lexed.tokens().stream()
                .filter(t -> t.kind() != SyntaxKind.EOF).toList();
        return lexed.errors().isEmpty() && code.size() == 1
                && code.getFirst().kind() == SyntaxKind.TYPEVAR;
    }

    @SuppressWarnings("unchecked")
    private static String matchOf(String entry) {
        Map<String, Object> grammar = (Map<String, Object>) JSON.readValue(
                TmLanguageGenerator.generate(), Object.class);
        Map<String, Object> repository = (Map<String, Object>) grammar.get("repository");
        return (String) ((Map<String, Object>) repository.get(entry)).get("match");
    }
}
