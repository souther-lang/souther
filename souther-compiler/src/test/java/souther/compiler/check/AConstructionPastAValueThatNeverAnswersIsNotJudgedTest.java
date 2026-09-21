package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A construction after a value that answers nothing is not judged, as one after any evaluation that
 * answers nothing is not.
 *
 * <p>{@code Int.truncatingDivide} answers no number for the one pair whose quotient no {@code Int}
 * holds, and aborts, so a value that is that quotient is one every run stops at. The invariant check
 * reads the value once, where it is held, and whether it comes back is a fact about what it does
 * and not about which build asked: it is carried to every build, and where the value does not come
 * back, nothing written after the build is reached and nothing there is refused.
 */
class AConstructionPastAValueThatNeverAnswersIsNotJudgedTest {

    private static String model(String dividend) {
        return """
                module m exposing (f, Negative)

                data Negative = Int
                    invariant value < 0

                let quotient = Int.truncatingDivide(%s, 0 - 1)

                behavior f : (x: Int) -> Negative
                    constructs Negative
                let f (x) = {
                    guard x >= 0 else Negative(0 - 1)
                    match quotient with
                        | Int as q -> Negative(x)
                        | DivisionByZero -> Negative(0 - 1)
                }
                """.formatted(dividend);
    }

    @Test
    void theConstructionAfterTheValueIsNotJudged() {
        assertDoesNotThrow(() -> Compiler.compile(model("(0 - 9223372036854775807) - 1")),
                "`x` is not below nought where `Negative(x)` stands, but no run gets past the"
                        + " quotient of the smallest whole number by minus one");
    }

    @Test
    void theSameConstructionAfterAValueThatDoesAnswerIsJudged() {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(model("10")),
                "a quotient that is a number comes back, so `Negative(x)` is reached");
        assertEquals("E2010", refused.getMessage().substring(0, 5), refused.getMessage());
    }
}
