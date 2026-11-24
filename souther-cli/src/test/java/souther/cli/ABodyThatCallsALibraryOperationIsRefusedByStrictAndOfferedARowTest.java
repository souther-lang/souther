package souther.cli;

import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body that calls a library operation whose copy has arms is refused by a strict build when its
 * one row runs none of the work, and is offered a row that does.
 *
 * <p>The copy of {@code List.take} has arms the body owes no row through. They are no fork of the
 * body's, so the body is asked whether a row tells it apart from answering one value, and the row
 * the search offers for that is a list with something in it to take.
 */
class ABodyThatCallsALibraryOperationIsRefusedByStrictAndOfferedARowTest {

    private static final String MODEL = """
            module repro.withtake

            data Pin = Int
                invariant value >= 1 && value <= 12

            data Throw = List<Pin>
                invariant List.allDistinctBy(p -> p, value)

            behavior points : (t: Throw) -> Int

            let points (t) = {
                let n = List.length(t.value)
                if n == 1 then List.sum(List.map(p -> p.value, t.value)) else n
            }

            example points
                | (Throw([])) -> 0
                | (Throw([Pin(12)])) -> 12
                | (Throw([Pin(1), Pin(2)])) -> 2
                | (Throw([Pin(1), Pin(2), Pin(3)])) -> 3

            behavior score : (throws: List<Throw>) -> Int

            let score (throws) = List.fold((acc, t) -> acc + points(t), 0, throws)

            example score
                | ([]) -> 0
                | ([Throw([Pin(12)])]) -> 12
                | ([Throw([Pin(12)]), Throw([Pin(1), Pin(2)])]) -> 14

            behavior running : (throws: List<Throw>) -> List<Int>

            let running (throws) =
                List.mapIndexed((i, _) -> score(List.take(i, throws)), throws)

            example running
                | ([]) -> []
            """;

    @Test
    void oneRowThatRunsNoneOfTheWorkIsRefusedByStrict() throws Exception {
        CliProcess.Ran strict = CliInProcess.run("examples", "--strict", written().toString());

        assertEquals(1, strict.code(), strict.out());
        assertTrue(strict.out().contains("no row would come out differently if the body always"
                + " answered what `running"), strict.out());
    }

    @Test
    void theRowOfferedForItGivesTheListSomethingToTakeFrom() throws Exception {
        String generated = CliInProcess.printed("examples", "--generate", written().toString());

        List<String> offered = generated.lines()
                .dropWhile(line -> !line.equals("example running"))
                .skip(1)
                .takeWhile(line -> line.startsWith("    |") || line.startsWith("//"))
                .filter(line -> line.startsWith("    |"))
                .toList();
        assertFalse(offered.isEmpty(), generated);
        assertTrue(offered.stream().allMatch(line -> line.contains("Throw(")
                        && !line.contains(": ([]) ->")),
                () -> "a row of `running` whose list holds a throw: " + generated);
    }

    private static Path written() throws Exception {
        Path file = Files.createTempDirectory("souther-take").resolve("withtake.sou");
        Files.writeString(file, MODEL);
        return file;
    }
}
