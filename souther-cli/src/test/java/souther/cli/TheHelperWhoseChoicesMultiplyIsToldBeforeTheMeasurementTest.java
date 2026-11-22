package souther.cli;

import org.junit.jupiter.api.Test;
import souther.cli.CliProcess.Ran;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@code souther examples} says, on the error stream and before it measures, which helper to
 * declare as a behavior where the values of a condition are made through more choices than one
 * condition is read on.
 *
 * <p>Said of how the values are written, so a model whose choices each come out one way, which
 * costs nothing to measure, is told the same as one whose choices multiply.
 */
class TheHelperWhoseChoicesMultiplyIsToldBeforeTheMeasurementTest {

    private static final int CHOICES = 7;

    private static final String MODEL = """
            module told

            let kept (n: Int): Int = if 1 < 2 then n else 0

            behavior zero : (n0: Int) -> Bool
            let zero (n0) = {
            """ + IntStream.range(0, CHOICES)
            .mapToObj(i -> "    let n" + (i + 1) + " = kept(n" + i + ")\n")
            .collect(Collectors.joining()) + "    n" + CHOICES + " == 0\n}\n" + """

            behavior same : (n: Int) -> Int
            let same (n) = n

            example zero
                | "nought" : (0) -> true

            example same
                | "one" : (1) -> 1
            """;

    private static List<String> saidAhead(String... more) throws Exception {
        Path file = Files.createTempDirectory("souther-told-ahead").resolve("told.sou");
        Files.writeString(file, MODEL);
        List<String> args = new ArrayList<>(List.of("examples", file.toString()));
        args.addAll(List.of(more));
        Ran ran = CliInProcess.run(args.toArray(String[]::new));
        assertEquals(0, ran.code(), ran.err());
        return ran.err().lines().filter(line -> line.contains("made through choices")
                || line.contains("選択を通して")).toList();
    }

    @Test
    void theHelperIsNamedWithTheConditionsItsChoicesAreTakenOutOf() throws Exception {
        assertEquals(List.of("before the lines are measured: in `told.zero`, the values of some"
                + " conditions (1) are made through choices that may take more than 512 readings"
                + " of one condition, which is as many as this compiler makes. Declared as a"
                + " behavior, `kept` is read as one answer, and the choices written in it are"
                + " taken out of those conditions (1)"), saidAhead());
    }

    @Test
    void itIsSaidInTheLanguageAskedFor() throws Exception {
        assertEquals(List.of("線を測る前に: `told.zero` では、値が多くの選択を通して作られている条件が 1 個あり、"
                + "このコンパイラが 1 つの条件を読む回数の上限（512 回）を超えるかもしれません。"
                + "`kept` を behavior として宣言すると、その答えは 1 つの値として読まれ、"
                + "そのうち 1 個の条件から `kept` に書かれた選択がなくなります"), saidAhead("--lang", "ja"));
    }

    @Test
    void itIsSaidOfTheBehaviorsThatAreMeasuredAndOfNoOther() throws Exception {
        assertEquals(List.of(), saidAhead("--behavior", "same"));
    }
}
