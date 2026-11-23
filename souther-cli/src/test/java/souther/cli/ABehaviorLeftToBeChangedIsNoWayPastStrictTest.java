package souther.cli;

import org.junit.jupiter.api.Test;
import souther.cli.CliProcess.Ran;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther examples} leaves a behavior unmeasured where its author is told what to change and
 * measuring it stops at a figure, which is no failure of its own; {@code --strict} refuses it and
 * changes nothing the run writes but that.
 *
 * <p>The model is two arms through six choices one after another, each over an input of its own,
 * which is the fewest whose readings a condition's author is told of at the figures declared.
 */
class ABehaviorLeftToBeChangedIsNoWayPastStrictTest {

    static final String MODEL = """
            module left

            behavior paid : (n0: Int, h0: Int, h1: Int, h2: Int, h3: Int, h4: Int, h5: Int) -> Bool
            let paid (n0, h0, h1, h2, h3, h4, h5) = {
                let n1 = (if n0 < h0 then n0 else h0) + 1
                let n2 = (if n1 < h1 then n1 else h1) + 1
                let n3 = (if n2 < h2 then n2 else h2) + 1
                let n4 = (if n3 < h3 then n3 else h3) + 1
                let n5 = (if n4 < h4 then n4 else h4) + 1
                let n6 = (if n5 < h5 then n5 else h5) + 1
                n6 == 0
            }
            """;

    @Test
    void strictRefusesItAndWritesTheSameReport() throws Exception {
        Path file = Files.createTempDirectory("souther-left").resolve("left.sou");
        Files.writeString(file, MODEL);

        Ran ran = CliInProcess.run("examples", file.toString());
        Ran strict = CliInProcess.run("examples", file.toString(), "--strict");

        assertEquals(0, ran.code(), ran.err());
        assertTrue(ran.out().contains("not measured: as it is written, measuring it stops at"),
                ran.out());
        assertTrue(ran.err().lines().anyMatch(line -> line.contains("`left.paid`")
                && line.contains("`--to-the-end`")), ran.err());
        assertEquals(1, strict.code(), strict.err());
        assertEquals(ran.out(), strict.out());
    }
}
