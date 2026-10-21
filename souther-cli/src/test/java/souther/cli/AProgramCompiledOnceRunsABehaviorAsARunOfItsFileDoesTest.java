package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A behavior run from a program compiled once answers what a run of the file answers.
 *
 * <p>{@link Runner#compile(Path)} keeps a compilation for runs to come, and {@link Runner#run(Path,
 * String, String)} compiles the file for the one run it makes. The second is the first followed by
 * one run, so the two can part only where a kept compilation answers otherwise the second time it is
 * asked, or where one run leaves behind something the next one reads. Asked of behaviors whose answers
 * are written differently — a record, a case of a sum, a list, a number — each run twice and in turn,
 * and of the behavior a file runs when none is named.
 */
class AProgramCompiledOnceRunsABehaviorAsARunOfItsFileDoesTest {

    private static final String MODEL = """
            module demo

            data Pair = { left: Int, right: Int }
            data Hit = { score: Int }
            data Miss
            data Outcome = Hit | Miss

            behavior paired : (a: Int, b: Int) -> Pair
            let paired (a, b) = Pair { left = a, right = b }

            behavior judged : (n: Int) -> Outcome
            let judged (n) = if n > 3 then Hit { score = n } else Miss

            behavior doubled : (xs: List<Int>) -> List<Int>
            let doubled (xs) = List.map(x -> x * 2, xs)

            behavior counted : (xs: List<Int>) -> Int
            let counted (xs) = List.length(xs)
            """;

    private record Asked(String behavior, String input) {}

    private static final List<Asked> ASKED = List.of(
            new Asked("paired", "[3, 7]"),
            new Asked("judged", "5"),
            new Asked("judged", "1"),
            new Asked("doubled", "[1, 2, 3]"),
            new Asked("counted", "[]"));

    @Test
    void eachBehaviorAnswersAsARunOfTheFileDoesWhateverRanBeforeIt(@TempDir Path dir)
            throws Exception {
        Path file = Files.writeString(dir.resolve("demo.sou"), MODEL);
        Runner.Program program = Runner.compile(file);
        for (int round = 0; round < 2; round++) {
            for (Asked each : ASKED) {
                assertEquals(Runner.run(file, each.behavior(), each.input()),
                        program.run(each.behavior(), each.input()),
                        () -> each + ", run from the program after the ones before it");
            }
        }
    }

    @Test
    void theBehaviorRunWhenNoneIsNamedIsTheOneARunOfTheFilePicks(@TempDir Path dir)
            throws Exception {
        Path file = Files.writeString(dir.resolve("one.sou"), """
                module demo

                behavior greet : (who: String) -> String
                let greet (who) = String.concat(["Hi, ", who])
                """);
        assertEquals(Runner.run(file, null, "\"Souther\""),
                Runner.compile(file).run(null, "\"Souther\""));
    }
}
