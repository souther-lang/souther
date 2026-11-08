package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;

import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The page a person reads is written in the language they named, line for line, and the rows
 * offered beside it are the same source whichever that is.
 *
 * <p>One model, compiled once and written in two languages. It has a line of its own the report
 * names under a behavior, a declaration's line with a point no row is owed at, and a row to offer —
 * which between them reach the sentence kinds a page is made of: a measure, a mark, a reason, a
 * rule handle said inside a sentence, and a comment on an offered row.
 */
class ThePageIsWrittenInTheLanguageNamedTest {

    private static final String LOGIN = """
            module example.login

            data Password = String
                invariant String.length(value) >= 1
            data Account = { password: Password }

            behavior login : (account: Account, given: Password) -> Allowed | Refused

            let login (account, given) =
                if account.password /= given then Refused else Allowed

            example login
                | (Account { password = Password("a") }, Password("a")) -> Allowed
            """;

    /** How a message that reached a sentence as a value rather than as words would read. */
    private static final Pattern A_VALUE_AND_NOT_WORDS = Pattern.compile("\\w\\[(\\]|\\w+=)");

    private static final Compiled COMPILED = new Compiled();

    /** The model and what this run offers for it, asked once for every test here. */
    private static final class Compiled {
        final Compilation compilation = Compilation.ofSource(LOGIN, "Main");
        final Map<String, Offering> offered;
        final SourceRendering rendering;

        Compiled() {
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            offered = GeneratedRows.offered(compilation, null, null);
            rendering = SourceRendering.namedByIdentity(compilation.texts());
        }

        List<String> page(Locale language) {
            return AdequacyReport.of(compilation, offered).human(rendering, language).lines()
                    .toList();
        }

        List<String> rows(Locale language) {
            return GeneratedRows.of(compilation, rendering, offered).text(language).lines()
                    .toList();
        }
    }

    /**
     * Every line of the page is said in the language named, and in the same place.
     *
     * <p>Line for line, because which lines a page says and in which order is decided in the base
     * wording and not by a translation. A line that came out the same in both is one left in
     * English; a heading that is a declaration's name is the name in every language.
     */
    @Test
    void everyLineOfThePageIsSaidInTheLanguageNamed() {
        List<String> english = COMPILED.page(Locale.ENGLISH);
        List<String> japanese = COMPILED.page(Locale.JAPANESE);

        assertEquals(english.size(), japanese.size(),
                () -> String.join("\n", english) + "\n---\n" + String.join("\n", japanese));
        for (int i = 0; i < english.size(); i++) {
            if (!english.get(i).isBlank() && !english.get(i).strip().matches("[\\w.]+")) {
                assertNotEquals(english.get(i), japanese.get(i), "a line left in English");
            }
            for (String line : List.of(english.get(i), japanese.get(i))) {
                assertFalse(A_VALUE_AND_NOT_WORDS.matcher(line).find(),
                        () -> "a part of the sentence is printed as the value it was: " + line);
            }
        }
        assertTrue(english.stream().anyMatch(line -> line.contains("invariant Password")),
                () -> "the declaration's line is said on the page: " + String.join("\n", english));
        assertTrue(japanese.stream().anyMatch(line -> line.contains("テストケース")),
                () -> "a row is the word the spec gives it: " + String.join("\n", japanese));
    }

    /** The rows are the same source in both, and only the comments around them are the reader's. */
    @Test
    void theRowsAreTheSameSourceAndOnlyTheirCommentsAreTranslated() {
        List<String> english = COMPILED.rows(Locale.ENGLISH);
        List<String> japanese = COMPILED.rows(Locale.JAPANESE);

        assertEquals(english.size(), japanese.size(), () -> english + "\n---\n" + japanese);
        assertTrue(english.stream().anyMatch(line -> !line.startsWith("//")),
                () -> "the block offers a row: " + english);
        for (int i = 0; i < english.size(); i++) {
            if (english.get(i).startsWith("//")) {
                assertNotEquals(english.get(i), japanese.get(i), "a comment left in English");
            } else {
                assertEquals(english.get(i), japanese.get(i), "a row is source either way");
            }
        }
    }
}
