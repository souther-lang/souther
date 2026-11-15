package souther.cli;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import souther.cli.CliProcess.Ran;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A comparison on the distance between an input and a value that is constant in pieces is read once
 * per piece, and each reading is a place of the line its author wrote.
 *
 * <p>{@code Int.abs} has two lines on the input for each piece, one where the difference is positive
 * and one where it is negative, and the comparison holds on opposite sides of them. A reading that
 * took its side from how the quantity faces the line alone placed the second of them beside a point
 * the author's line does not have.
 *
 * <p>Which point of the author's line each reading is, is
 * {@code ATwoOrdersTellTheirSidesApartByWhereEachHoldsTest}'s; this one asks that a model written
 * this way is read through, on a comparison that holds above its line and on one that holds below.
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

    /** The rows of "the distance is at least two", or of its negation where {@code atMost}. */
    private static String rows(boolean atMost) {
        return """
                example far
                    | "same" : (2, 150) -> %1$s
                    | "one up" : (1, 150) -> %1$s
                    | "two up" : (1, 250) -> %2$s
                    | "two down" : (3, 50) -> %2$s
                    | "one down" : (3, 250) -> %1$s
                """.formatted(atMost, !atMost);
    }

    private static String report(String body, boolean atMost) throws Exception {
        Path file = Files.createTempDirectory("souther-far").resolve("model.sou");
        Files.writeString(file, HEAD + body + "\n" + rows(atMost));
        Ran ran = CliInProcess.run("examples", "--format", "json", file.toString());
        assertEquals(0, ran.code(), ran.err());
        return ran.out();
    }

    @ParameterizedTest
    @CsvSource({">= 2,false", "> 1,false", "< 2,true", "<= 1,true"})
    void theStepMinusTheInputIsTied(String comparison, boolean atMost) throws Exception {
        assertFalse(report("let far (current, pay) = Int.abs(gradeOf(pay) - current) "
                + comparison, atMost).contains("a_reading_not_tied_to_its_line"));
    }

    @ParameterizedTest
    @CsvSource({">= 2,false", "> 1,false", "< 2,true", "<= 1,true"})
    void theInputMinusTheStepIsTied(String comparison, boolean atMost) throws Exception {
        assertFalse(report("let far (current, pay) = Int.abs(current - gradeOf(pay)) "
                + comparison, atMost).contains("a_reading_not_tied_to_its_line"));
    }
}
