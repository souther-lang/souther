package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule over what an operation answers, where the library defines it in cases of arithmetic over
 * what it was given, is read on each case: where the case is reached, the rule is the rule over the
 * arithmetic that case answers.
 *
 * <p>{@code Int.abs(n)} answers {@code 0 - n} where {@code n} is below nought and {@code n} from
 * there, which is what its body was proved to answer. So {@code Int.abs(n) > 5} holds where
 * {@code n} is below minus five or past five: two lines on {@code n}, and nothing unread. Where the
 * cases part, at nought, is the library's and no rule of the model: the rule comes out the same on
 * both sides of it.
 *
 * <p>The same wherever the call stands in the arithmetic of the rule, and whichever library the
 * operation is of.
 */
class AnOperationAnsweringArithmeticByCasesIsReadOnEachCaseTest {

    @Test
    void eachCaseDrawsTheLinesOfTheArithmeticItAnswers() {
        Map<String, String> read = new LinkedHashMap<>();
        read.put("the call as a side", reading("Int", "n: Int", "Int.abs(n) > 5"));
        read.put("the call inside a sum", reading("Int", "n: Int", "Int.abs(n) + 1 > 6"));

        String lines = "[n/x < -5, n/-5 <= x <= 5, n/5 < x] unread []";
        assertEquals(Map.of("the call as a side", lines, "the call inside a sum", lines), read);
    }

    @Test
    void theDecimalOneIsReadTheSameWay() {
        assertEquals("[d/x < -5, d/-5 <= x <= 5, d/5 < x] unread []",
                reading("Decimal", "d: Decimal", "Decimal.abs(d) > 5.0m"));
    }

    private static String reading(String library, String parameter, String condition) {
        return MeasuredBehavior.reading("""
                module g

                data Yes
                data No

                behavior classify : (%s) -> Yes | No
                let classify (%s) = if %s then Yes else No

                example classify
                    | "one" : (%s) -> No
                """.formatted(parameter, parameter.substring(0, parameter.indexOf(':')), condition,
                library.equals("Int") ? "1" : "1.0m"), "classify");
    }
}
