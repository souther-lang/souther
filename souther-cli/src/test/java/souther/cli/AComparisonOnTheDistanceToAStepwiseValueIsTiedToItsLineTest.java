package souther.cli;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import souther.cli.CliProcess.Ran;
import souther.compiler.UnreadBesideItsStops;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.function.IntPredicate;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison on the distance between an input and a value that is constant in pieces is read
 * once per piece, and each reading is a place of the line its author wrote.
 *
 * <p>{@code Int.abs} has two lines on the input for each piece, one where the difference is
 * positive and one where it is negative, and the comparison holds on opposite sides of them. With a
 * row on each side of each of them, and at each place the step changes, every point the author's
 * line owes a row is met. That every one of them is is the part of this that says the readings
 * were each tied to the point they are: a reading tied to a neighbour's point leaves the points of
 * its own line unmet however many rows there are.
 *
 * <p>Which point of the author's line each reading is, is
 * {@code AReadingIsTiedToTheAuthorsPointOfTheSameValuesTest}'s. This asks that a model written this
 * way is read through, on a comparison that holds beside its line and on one that holds away from
 * it, with the difference taken either way round.
 */
class AComparisonOnTheDistanceToAStepwiseValueIsTiedToItsLineTest {

    private static final String HEAD = """
            module example.far

            let gradeOf (x: Int): Int =
                if x < 100 then 1
                else if x < 200 then 2
                else if x < 300 then 3
                else 4

            behavior far : (current: Int, pay: Int) -> Bool
            """;

    private static final int[] PAYS = {50, 99, 100, 150, 199, 200, 250, 299, 300, 350};

    private static int gradeOf(int pay) {
        return pay < 100 ? 1 : pay < 200 ? 2 : pay < 300 ? 3 : 4;
    }

    static Stream<Arguments> comparisons() {
        return Stream.of(
                Arguments.of("gradeOf(pay) - current", ">= 2", (IntPredicate) d -> d >= 2),
                Arguments.of("gradeOf(pay) - current", "> 1", (IntPredicate) d -> d > 1),
                Arguments.of("gradeOf(pay) - current", "< 2", (IntPredicate) d -> d < 2),
                Arguments.of("gradeOf(pay) - current", "<= 1", (IntPredicate) d -> d <= 1),
                Arguments.of("current - gradeOf(pay)", ">= 2", (IntPredicate) d -> d >= 2),
                Arguments.of("current - gradeOf(pay)", "< 2", (IntPredicate) d -> d < 2));
    }

    /** A row at each of the values of {@code current} either side of every line, at each pay. */
    private static String rows(IntPredicate holds) {
        StringBuilder rows = new StringBuilder("example far\n");
        for (int pay : PAYS) {
            for (int current = -2; current <= 8; current++) {
                rows.append("    | \"%d_%d\" : (%d, %d) -> %s%n".formatted(
                        current, pay, current, pay,
                        holds.test(Math.abs(gradeOf(pay) - current))));
            }
        }
        return rows.toString();
    }

    @ParameterizedTest
    @MethodSource("comparisons")
    void everyPointTheAuthorsLineOwesARowIsMet(String difference, String comparison,
                                               IntPredicate holds) throws Exception {
        Path file = Files.createTempDirectory("souther-far").resolve("model.sou");
        Files.writeString(file, HEAD + "let far (current, pay) = Int.abs(" + difference + ") "
                + comparison + "\n\n" + rows(holds));
        Ran ran = CliInProcess.run("examples", file.toString());
        assertEquals(0, ran.code(), ran.err());
        // The grade less a current of any whole number may pass an Int, and so may its absolute
        // value, where nothing in the comparison tells: that is said of the run, and every reading
        // is read through all the same.
        assertFalse(UnreadBesideItsStops.in(ran.out()), ran.out());
        assertTrue(ran.out().contains("obligations 42/42"), ran.out());
    }
}
