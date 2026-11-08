package souther.cli;

import souther.cli.CliProcess.Ran;
import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther examples} writes the page a person reads in the language they named, and the
 * document a consumer parses in the same words whichever they named.
 *
 * <p>Asked of the command, because what is held is what a reader is handed: the flag reaches the
 * page and the comments of the rows beside it, and stops short of the document and of the rows
 * themselves, which are source an author pastes.
 */
class AnExamplesReportIsWrittenInTheLanguageNamedTest {

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

    /** Where the rows begin, which is the first comment the block writes. */
    private static final String THE_ROWS = "// ";

    /**
     * The page says the same lines in the same order, and every one of them in the words of the
     * language named.
     *
     * <p>Line for line, because which lines a page says and in which order is decided in the base
     * wording and not by a translation. A line that came out the same in both languages is one this
     * left in English.
     */
    @Test
    void everyLineOfThePageIsSaidInTheLanguageNamed() throws Exception {
        Path model = model();
        List<String> english = page(examples(model, "en"));
        List<String> japanese = page(examples(model, "ja"));

        assertEquals(english.size(), japanese.size(),
                () -> "one line for each line, whichever language says it:\n"
                        + String.join("\n", english) + "\n---\n" + String.join("\n", japanese));
        for (int i = 0; i < english.size(); i++) {
            // A heading that is a declaration's name is the name in every language.
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
                () -> "what the report calls a row is the word the spec gives it: "
                        + String.join("\n", japanese));
    }

    /** The rows are the same source in both, and only the comments around them are the reader's. */
    @Test
    void theRowsAreTheSameSourceAndOnlyTheirCommentsAreTranslated() throws Exception {
        Path model = model();
        List<String> english = rows(examples(model, "en", "--generate"));
        List<String> japanese = rows(examples(model, "ja", "--generate"));

        assertEquals(english.size(), japanese.size(), () -> english + "\n---\n" + japanese);
        assertTrue(english.stream().anyMatch(line -> !line.startsWith(THE_ROWS)),
                () -> "the block offers a row: " + english);
        for (int i = 0; i < english.size(); i++) {
            if (english.get(i).startsWith(THE_ROWS)) {
                assertNotEquals(english.get(i), japanese.get(i), "a comment left in English");
            } else {
                assertEquals(english.get(i), japanese.get(i), "a row is source either way");
            }
        }
    }

    /** The document is the same document whichever language was named. */
    @Test
    void theDocumentIsTheSameWhicheverLanguageWasNamed() throws Exception {
        Path model = model();
        Ran english = CliInProcess.run("examples", "--format", "json", "--lang", "en",
                model.toString());
        Ran japanese = CliInProcess.run("examples", "--format", "json", "--lang", "ja",
                model.toString());

        assertEquals(0, english.code(), english::err);
        assertTrue(english.out().startsWith("{"), english::out);
        assertEquals(english.out(), japanese.out());
    }

    private static List<String> page(String printed) {
        return printed.lines().takeWhile(line -> !line.startsWith(THE_ROWS)).toList();
    }

    private static List<String> rows(String printed) {
        return printed.lines().dropWhile(line -> !line.startsWith(THE_ROWS)).toList();
    }

    private static Path model() throws Exception {
        Path file = Files.createTempDirectory("souther-lang").resolve("login.sou");
        Files.writeString(file, LOGIN);
        return file;
    }

    private static String examples(Path model, String language, String... more) {
        String[] args = new String[4 + more.length];
        args[0] = "examples";
        args[1] = "--lang";
        args[2] = language;
        System.arraycopy(more, 0, args, 3, more.length);
        args[args.length - 1] = model.toString();
        return CliInProcess.printed(args);
    }
}
