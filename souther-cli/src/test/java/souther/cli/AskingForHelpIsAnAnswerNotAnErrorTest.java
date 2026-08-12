package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What this command line takes is something it can be asked, rather than something it says while
 * refusing a line.
 *
 * <p>The usage text was reachable only from a failure — no command, an unknown one, an argument
 * missing — so it went to stderr under a non-zero exit code every time. An author who wanted to read
 * it had to write a line they knew to be wrong, and a reader piping the answer got nothing.
 *
 * <p>What is asked here is which section a line asks for and where the answer goes, and never what
 * any of it says. The wording is the renderer's, and a test that reads it back holds this command
 * line to the sentence it happens to print today.
 */
class AskingForHelpIsAnAnswerNotAnErrorTest {

    private record Said(int code, String err, String out) {}

    /** Runs the command line and answers with its exit code and what it wrote. */
    private Said run(String... args) {
        PrintStream originalErr = System.err;
        PrintStream originalOut = System.out;
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            int code = Main.dispatch(args);
            return new Said(code, err.toString(StandardCharsets.UTF_8),
                    out.toString(StandardCharsets.UTF_8));
        } finally {
            System.setErr(originalErr);
            System.setOut(originalOut);
        }
    }

    // --- where the answer goes ---------------------------------------------------------------

    /** On stdout under a zero exit code: it is what was asked for, not a refusal. */
    @Test
    void helpIsAnsweredOnStdout() {
        Said said = run("help");

        assertEquals(0, said.code(), said.err());
        assertEquals("", said.err());
        assertFalse(said.out().isEmpty());
    }

    /** The option at the command position asks the same thing, and is answered the same way. */
    @Test
    void theHelpOptionOnItsOwnIsTheHelpCommand() {
        for (String spelling : new String[] {"--help", "-h"}) {
            Said said = run(spelling);

            assertEquals(0, said.code(), spelling + ": " + said.err());
            assertEquals("", said.err(), spelling);
            assertFalse(said.out().isEmpty(), spelling);
        }
    }

    /** A command line that names no command is still a line this compiler refuses. */
    @Test
    void anEmptyCommandLineIsStillRefused() {
        Said said = run();

        assertEquals(2, said.code());
        assertEquals("", said.out());
        assertFalse(said.err().isEmpty());
    }

    // --- which section a line asks for --------------------------------------------------------

    /**
     * Every command can be asked about, and each is answered with its own section.
     *
     * <p>A row per command, and the answer is the command itself rather than a count or a
     * non-emptiness: a resolution that gave every name the same section would satisfy anything
     * weaker. {@code help} is one of the rows — it is a command like the others, and a table that
     * carries it as a name the dispatch happens to know would have nothing to say when asked about
     * it.
     */
    @Test
    void everyCommandCanBeAskedAbout() {
        for (CliCommand command : CliCommand.values()) {
            assertSame(command, Main.helpTarget(new String[] {command.spelling()}),
                    command.spelling());

            Said said = run("help", command.spelling());

            assertEquals(0, said.code(), command.spelling() + ": " + said.err());
            assertEquals("", said.err(), command.spelling());
            assertFalse(said.out().isEmpty(), command.spelling());
        }
    }

    /** Asking about it by the option is asking about it by name. */
    @Test
    void theHelpOptionNamesTheCommandItIsWrittenOn() {
        for (CliCommand command : CliCommand.values()) {
            assertTrue(CliOption.read(command.spelling(), new String[] {"--help"}).help(),
                    command.spelling());
            assertTrue(CliOption.read(command.spelling(), new String[] {"-h"}).help(),
                    command.spelling());
        }
    }

    /** A word that is no command of this compiler's is refused rather than answered with the lot. */
    @Test
    void helpAboutSomethingThatIsNotACommandIsRefused() {
        assertNull(Main.helpTarget(new String[] {"nope"}));

        Said said = run("help", "nope");

        assertEquals(2, said.code());
        assertFalse(said.err().isEmpty());
    }

    /** It answers about one command, so a line naming two has not said which. */
    @Test
    void helpAboutTwoCommandsIsRefused() {
        Said said = run("help", "compile", "run");

        assertEquals(2, said.code());
        assertFalse(said.err().isEmpty());
    }

    // --- what makes a line a request for help -------------------------------------------------

    /**
     * A token in the position of an option's value is that value, whatever it is spelt like.
     *
     * <p>This is why the question is asked by the walk that reads the options and not by a search
     * through the tokens: {@code --input --help} is a line handing {@code run} the input
     * {@code --help}, and a search finds a request for help in it. The two readings part company
     * exactly here.
     */
    @Test
    void anOptionsValueIsNotARequestForHelp() {
        assertFalse(CliOption.read("run",
                new String[] {"m.sou", "--input", "--help"}).help());

        Said said = run("run", "m.sou", "--input", "--help");

        assertNotEquals(0, said.code());
    }

    /**
     * A line this compiler would refuse is still a line asking what the command takes, and that is
     * what it is answered with — whichever side of the refusal the option was written on.
     *
     * <p>Both orders, because a walk that stopped at its first refusal would answer the first of
     * these and not the second.
     */
    @Test
    void helpIsAnsweredBeforeTheLineIsRefused() {
        for (String[] line : new String[][] {
                {"--nonsense", "--help"},
                {"--help", "--nonsense"}}) {
            CliOption.Reading read = CliOption.read("run", line);

            assertTrue(read.help(), String.join(" ", line));
            assertNotNull(read.refusal(), String.join(" ", line));

            Said said = run("run", line[0], line[1]);

            assertEquals(0, said.code(), String.join(" ", line) + ": " + said.err());
            assertEquals("", said.err(), String.join(" ", line));
        }
    }

    // --- the table the sections are written from ----------------------------------------------

    /**
     * Every option a command takes has something to say under it, and every command has something
     * to say about itself.
     *
     * <p>The defect this refuses is an option added to the table and left undescribed: it is listed
     * in the section of every command that takes it, and what a reader is shown beside it is a
     * blank. Asked of the table rather than of the text, so it is the answer the renderer would
     * print that is held and not the shape it prints it in.
     */
    @Test
    void everyOptionACommandTakesIsDescribedUnderIt() {
        for (CliCommand command : CliCommand.values()) {
            assertFalse(command.summary().isBlank(), command.spelling());

            int described = 0;
            for (CliOption option : CliOption.values()) {
                if (!option.ownedBy(command.spelling())) {
                    continue;
                }
                assertFalse(command.describe(option).isBlank(),
                        command.spelling() + " " + option.spelling());
                described++;
            }
            assertTrue(described > 0, command.spelling() + " takes no option at all");
        }
    }

    /** An option that takes a value says what the value is; one that takes none says nothing. */
    @Test
    void anOptionSpellsItsValueWhereItTakesOne() {
        for (CliOption option : CliOption.values()) {
            if (option.takesAValue()) {
                assertFalse(option.valueSpelling().isBlank(), option.spelling());
            } else {
                assertNull(option.valueSpelling(), option.spelling());
            }
        }
    }
}
