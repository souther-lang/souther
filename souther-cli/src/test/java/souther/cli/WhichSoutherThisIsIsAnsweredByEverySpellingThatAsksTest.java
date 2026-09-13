package souther.cli;

import souther.compiler.meta.ModuleMetadata;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reader who has just installed this asks which Souther they got, and is answered whichever word
 * they reach for.
 *
 * <p>Neither spelling was a command, so both ended on {@code unknown command} and the install flows
 * had nothing to end on but {@code souther help}, which answers a different question.
 *
 * <p>What is asked here is that the answer is a reading of the manifest and never a version written
 * down beside it. The value is {@code unreleased} under a test, which is what running from class
 * files means; that it is the same value the compiler reads of itself is the whole of the claim, and
 * a literal put back here would be a different one.
 */
class WhichSoutherThisIsIsAnsweredByEverySpellingThatAsksTest {

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

    /** What every spelling has to write, read where the compiler reads it. */
    private static String theReading() {
        return "souther " + ModuleMetadata.compilerVersion();
    }

    @Test
    void theCommandIsAnsweredOnStdout() {
        Said said = run("version");

        assertEquals(0, said.code(), said.err());
        assertEquals("", said.err());
        assertEquals(theReading(), said.out().strip());
    }

    /** The option at the command position asks the same thing, and is answered the same way. */
    @Test
    void theOptionOnItsOwnIsTheCommand() {
        Said said = run("--version");

        assertEquals(0, said.code(), said.err());
        assertEquals("", said.err());
        assertEquals(theReading(), said.out().strip());
    }

    /**
     * Every command takes it, and answers it instead of running. Which compiler read the line is
     * not a question about the line, so the command it was written under does not change the answer.
     */
    @Test
    void theOptionUnderACommandAnswersRatherThanRunningIt() {
        Said said = run("compile", "--version");

        assertEquals(0, said.code(), said.err());
        assertEquals("", said.err());
        assertEquals(theReading(), said.out().strip());
    }

    /** And ahead of what is wrong with the line, which is why nothing wrong with one is asserted. */
    @Test
    void theOptionOutranksARefusalOfTheLine() {
        Said said = run("compile", "--nonsense", "--version");

        assertEquals(0, said.code(), said.err());
        assertEquals(theReading(), said.out().strip());
    }

    /** The command takes nothing, and a line that gave it something is told what it gave. */
    @Test
    void anArgumentIsRefusedWhereThereIsNoOperandForItToBe() {
        Said said = run("version", "model.sou");

        assertEquals(2, said.code());
        assertTrue(said.err().contains("model.sou"), said.err());
        assertEquals("", said.out());
    }
}
