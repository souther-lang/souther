package souther.cli;

import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A login comparing the password it holds with the one it was given is offered the row a wrong
 * password is, and the block says nothing that row contradicts.
 *
 * <p>Written against the command, because what an author is handed is this block: the row with two
 * different passwords, and — once the right-password row is written — no line saying the arm a
 * wrong password takes cannot be steered into, nor that nothing offers a row for the answer the
 * rows above already give.
 */
class APasswordComparedIsOfferedARowEachWayTest {

    private static final String LOGIN = """
            module example.login

            data Password = String
            data Account = { password: Password }

            behavior login : (account: Account, given: Password) -> Allowed | Refused

            let login (account, given) =
                if account.password /= given then Refused else Allowed
            """;

    @Test
    void aWrongPasswordIsOfferedARowBesideTheRightOne() throws Exception {
        String out = examples(LOGIN);

        assertTrue(out.contains("(Account { password = Password(\"\") }, Password(\"\"))"),
                () -> "the row where the two are one: " + out);
        assertTrue(out.contains("// fills a decision rule (the comparison at 9:25 holds)"),
                () -> "and a row for the rule where they differ: " + out);
        assertFalse(out.contains("? nothing could show a row can be written at a decision rule"),
                () -> "neither rule is left with nothing shown: " + out);
    }

    @Test
    void withTheRightPasswordWrittenTheBlockSaysNothingItsRowsContradict() throws Exception {
        String out = examples(LOGIN + """

                example login
                    | (Account { password = Password("") }, Password("")) -> Allowed
                """);

        assertTrue(out.contains("// fills a decision rule (the comparison at 9:25 holds)"),
                () -> "the wrong password is offered: " + out);
        assertFalse(out.contains("could not all be written down"),
                () -> "the way into the arm a wrong password takes is read: " + out);
        assertFalse(out.contains("nothing offers a row for `Refused`"),
                () -> "nothing says no row is offered for what the row above answers: " + out);
        assertTrue(out.contains("nothing aims a row at `Refused` in `login`"),
                () -> "what is said is that nothing searches by the answer: " + out);
    }

    private static String examples(String model) throws Exception {
        Path file = Files.createTempDirectory("souther-login").resolve("login.sou");
        Files.writeString(file, model);
        return CliInProcess.printed("examples", file.toString(), "--generate");
    }
}
