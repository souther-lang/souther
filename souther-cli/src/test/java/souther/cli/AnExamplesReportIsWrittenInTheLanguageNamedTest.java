package souther.cli;

import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code --lang} reaches the page {@code souther examples} writes and the comments of the rows it
 * offers.
 *
 * <p>The command's part and nothing else: that the language the flag names is the one handed to
 * both writers. What each writes in it is held where they write it
 * ({@code ThePageIsWrittenInTheLanguageNamedTest}). The document takes no language at all, so
 * there is nothing for the flag to reach there.
 */
class AnExamplesReportIsWrittenInTheLanguageNamedTest {

    private static final String LOGIN = """
            module example.login

            behavior login : (given: String) -> Allowed | Refused

            let login (given) = if given == "a" then Allowed else Refused
            """;

    @Test
    void theLanguageNamedReachesThePageAndTheRows() throws Exception {
        Path file = Files.createTempDirectory("souther-lang").resolve("login.sou");
        Files.writeString(file, LOGIN);

        String printed = CliInProcess.printed("examples", "--lang", "ja", "--generate",
                file.toString());

        assertTrue(printed.lines().anyMatch(line -> !line.startsWith("//")
                        && line.contains("テストケース")),
                () -> "the page is in the language named: " + printed);
        assertTrue(printed.lines().anyMatch(line -> line.startsWith("//")
                        && line.contains("テストケース")),
                () -> "and so are the comments of the rows: " + printed);
    }
}
