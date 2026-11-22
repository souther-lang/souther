package souther.cli;

import org.junit.jupiter.api.Test;
import souther.cli.CliProcess.Ran;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther examples} leaves a behavior unmeasured where its author is told what to change and
 * measuring it stops at a figure; {@code --strict} refuses it, and {@code --to-the-end} measures it.
 *
 * <p>The model is two arms through seven choices one after another, each over an input of its own:
 * the choices come to more readings of the last comparison than are made of one, which is what its
 * author is told of, and the cases of its lines to more than a statement is asked questions. The
 * behavior beside it is told of nothing, and its rows cover it.
 */
class ABehaviorLeftToBeChangedIsNoWayPastStrictTest {

    private static final String MODEL = """
            module left

            behavior paid : (n0: Int, h0: Int, h1: Int, h2: Int, h3: Int, h4: Int, h5: Int, h6: Int)
                -> Bool
            let paid (n0, h0, h1, h2, h3, h4, h5, h6) = {
                let n1 = (if n0 < h0 then n0 else h0) + 1
                let n2 = (if n1 < h1 then n1 else h1) + 1
                let n3 = (if n2 < h2 then n2 else h2) + 1
                let n4 = (if n3 < h3 then n3 else h3) + 1
                let n5 = (if n4 < h4 then n4 else h4) + 1
                let n6 = (if n5 < h5 then n5 else h5) + 1
                let n7 = (if n6 < h6 then n6 else h6) + 1
                n7 == 0
            }

            behavior same : (n: Int) -> Int
            let same (n) = n

            example same
                | "one" : (1) -> 1
                | "two" : (2) -> 2
            """;

    private static Ran examples(String... more) throws Exception {
        Path file = Files.createTempDirectory("souther-left").resolve("left.sou");
        Files.writeString(file, MODEL);
        List<String> args = new ArrayList<>(List.of("examples", file.toString()));
        args.addAll(List.of(more));
        return CliInProcess.run(args.toArray(String[]::new));
    }

    @Test
    void itIsNamedWithHowToMeasureItAllTheSameAndIsNoFailureOfItsOwn() throws Exception {
        Ran ran = examples();

        assertEquals(0, ran.code(), ran.err());
        assertTrue(ran.out().contains("not measured: as it is written, measuring it stops at"),
                ran.out());
        assertTrue(ran.err().lines().anyMatch(line -> line.contains("`left.paid`")
                && line.contains("`--to-the-end`")), ran.err());
        assertTrue(examples("--lang", "ja").err().lines().anyMatch(
                line -> line.contains("`left.paid`") && line.contains("`--to-the-end`")));
    }

    @Test
    void strictRefusesItAndWritesTheSameReport() throws Exception {
        Ran ran = examples("--strict");

        assertEquals(1, ran.code(), ran.err());
        assertEquals(examples().out(), ran.out());
    }

    /** Asked of a behavior that is measured, nothing is left and nothing is refused. */
    @Test
    void strictRefusesNothingOfABehaviorThatIsMeasured() throws Exception {
        Ran ran = examples("--strict", "--behavior", "same");

        assertEquals(0, ran.code(), ran.err());
        assertFalse(ran.err().contains("--to-the-end"), ran.err());
    }
}
