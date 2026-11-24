package souther.compiler.diag;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.jupiter.api.Test;

import souther.test.RepositoryJavaSources;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a message carries is values, and the words around them are the catalog's.
 *
 * <p>A value a message is filled with is printed as it is, in every language. A sentence handed to
 * a message as one of its values is therefore English wherever it is read: a Japanese reader was
 * told "ここでは it is a helper `let`, …", because the words were written at the throw site and
 * not in the catalog. So no message, and no phrase of the catalog's, is handed a string literal that
 * holds words: what varies is a name, a number or code, and what is said about it is an entry.
 *
 * <p>A tripwire and not a proof. It reads the source, so it sees a literal written in the arguments
 * of the construction and not one a helper returns: a sentence assembled elsewhere and handed over
 * as a variable is not seen here.
 */
class NoMessageIsHandedASentenceTest {

    /** Where a message is made, or a phrase of the catalog's: what follows is what it is filled with. */
    private static final Pattern MADE = Pattern.compile("new\\s+\\w+Message\\.\\w+\\(|Localizable\\.of\\(");
    private static final Pattern LITERAL = Pattern.compile("\"((?:[^\"\\\\]|\\\\.)*)\"");
    /** Two words with a space between, which is what a sentence has and a name or code does not. */
    private static final Pattern WORDS = Pattern.compile("[A-Za-z]{2,} [A-Za-z]{2,}");

    @Test
    void noMessageIsFilledWithWords() {
        Map<Path, String> sources = RepositoryJavaSources.forThisFork().mainTexts();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");
        List<String> handed = new ArrayList<>();
        sources.forEach((source, text) -> {
            Matcher made = MADE.matcher(text);
            while (made.find()) {
                String filledWith = argumentsAfter(text, made.end());
                boolean phrase = made.group().startsWith("Localizable");
                Matcher literal = LITERAL.matcher(filledWith);
                boolean first = true;
                while (literal.find()) {
                    // A phrase's first literal is its key.
                    if (phrase && first) {
                        first = false;
                        continue;
                    }
                    first = false;
                    if (WORDS.matcher(literal.group(1)).find()) {
                        int line = text.substring(0, made.start()).split("\n", -1).length;
                        handed.add(source.getFileName() + ":" + line + " " + made.group()
                                + " \"" + literal.group(1) + "\"");
                    }
                }
            }
        });
        assertEquals(List.of(), handed,
                "a message is handed a sentence, which is printed in English in every language;"
                        + " write the words as a catalog entry and hand over the values");
    }

    /** The text between the parenthesis that opened at {@code from} and the one that closes it. */
    private static String argumentsAfter(String text, int from) {
        int depth = 1;
        int at = from;
        while (at < text.length() && depth > 0) {
            char c = text.charAt(at);
            if (c == '"') {
                at++;
                while (at < text.length() && text.charAt(at) != '"') {
                    at += text.charAt(at) == '\\' ? 2 : 1;
                }
            } else if (c == '(') {
                depth++;
            } else if (c == ')') {
                depth--;
            }
            at++;
        }
        return text.substring(from, Math.max(from, at - 1));
    }
}
