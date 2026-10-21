package souther.cli;

import souther.cli.CliProcess.Ran;
import souther.compiler.meta.ModuleMetadata;

import org.junit.jupiter.api.Test;

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
        Ran ran = CliInProcess.run(args);
        return new Said(ran.code(), ran.err(), ran.out());
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

    /**
     * And ahead of what is wrong with the line: the answer is written and the refusal is not.
     *
     * <p>Both halves, because a line answered and refused at once is the shape this would otherwise
     * drift into — the version on stdout under a zero code, and the unknown option on stderr beside
     * it, which is a reader told their line is wrong by a run that did what they asked.
     */
    @Test
    void theOptionOutranksARefusalOfTheLine() {
        Said said = run("compile", "--nonsense", "--version");

        assertEquals(0, said.code(), said.err());
        assertEquals("", said.err());
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
