package souther.cli;

import org.junit.jupiter.api.Test;
import souther.cli.CliProcess.Ran;
import souther.test.Nightly;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther examples --to-the-end} measures a behavior a plain run leaves for its author to
 * change.
 *
 * <p>Deferred to the nightly: what is left is what stops at a figure, so a model the option makes a
 * difference to is measured up to one this command holds a compilation to, and no smaller one is
 * left there. What it finds is the option read and not handed on, which is as well found by the
 * morning.
 */
@Nightly
class ABehaviorLeftToBeChangedIsMeasuredToTheEndWhereAskedTest {

    @Test
    void itIsMeasuredAsItIsWritten() throws Exception {
        Path file = Files.createTempDirectory("souther-left").resolve("left.sou");
        Files.writeString(file, ABehaviorLeftToBeChangedIsNoWayPastStrictTest.MODEL);

        Ran ran = CliInProcess.run("examples", file.toString(), "--to-the-end");

        assertTrue(ran.out().contains("paid"), ran.out());
        assertFalse(ran.out().contains("not measured: as it is written"), ran.out());
        assertFalse(ran.err().contains("`--to-the-end`"), ran.err());
    }
}
