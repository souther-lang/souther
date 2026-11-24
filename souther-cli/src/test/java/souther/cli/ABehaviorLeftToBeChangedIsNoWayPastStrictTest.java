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
 * <p>The model is one condition over what ten choices answer, which is the fewest of two arms each
 * whose readings are past the figure of one condition's.
 */
class ABehaviorLeftToBeChangedIsNoWayPastStrictTest {

    static final String MODEL = """
            module left

            behavior paid : (f0: Bool, f1: Bool, f2: Bool, f3: Bool, f4: Bool, f5: Bool, f6: Bool,
                f7: Bool, f8: Bool, f9: Bool) -> Bool
            let paid (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) = {
                let one = (if f0 then 1 else 2) + (if f1 then 1 else 2) + (if f2 then 1 else 2)
                let two = (if f3 then 1 else 2) + (if f4 then 1 else 2) + (if f5 then 1 else 2)
                let three = (if f6 then 1 else 2) + (if f7 then 1 else 2) + (if f8 then 1 else 2)
                one + two + three + (if f9 then 1 else 2) == 12
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
