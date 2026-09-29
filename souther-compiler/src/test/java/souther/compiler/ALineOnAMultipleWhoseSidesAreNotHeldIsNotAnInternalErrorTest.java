package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

/**
 * A rule that writes a multiple of a position is read on the order of the written form, and the
 * values beside its line are then read back in the position's own units. A multiple small enough puts
 * a value beside the line at a whole number with more digits than any number the host builds, which
 * is a fact about the run and not about the values the position has. The reading says which of its
 * sides it could not work out; that it does so and does not stop with an internal error is what every
 * phase owes.
 *
 * <p>A model whose own example computes the multiple aborts at run time, and that is a diagnostic
 * like any other; only what is not one is an internal error.
 */
class ALineOnAMultipleWhoseSidesAreNotHeldIsNotAnInternalErrorTest {

    private static String squarings(int upTo) {
        StringBuilder chain = new StringBuilder("let sq (x: Decimal): Decimal = x * x\n\nlet t0 = 0.1m\n");
        for (int i = 1; i <= upTo; i++) {
            chain.append("let t").append(i).append(" = sq(t").append(i - 1).append(")\n");
        }
        return chain.toString();
    }

    private static String model(String squarings, String body, String example) {
        return """
                module probe.follow

                %s
                data A = Decimal
                data H = { a: A }
                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (h: H) -> Verdict
                let take (h) = { %s }

                %s
                """.formatted(squarings, body, example);
    }

    private static final String EXAMPLE = """
            example take
                | "one" : (H { a = A(50.0m) }) -> No
            """;

    /** Compiles the source, or is told why it does not: a diagnostic is an answer. */
    private static void isAnsweredWithoutAnInternalError(String source) {
        try {
            Compiler.compile(source);
        } catch (CompileException reported) {
            // A diagnostic about the model, which is what a phase that cannot say more owes.
        }
    }

    @Test
    void aMultipleWhoseValuesBesideItsLineAreBeyondTheHostIsNotAnInternalError() {
        isAnsweredWithoutAnInternalError(model(squarings(62),
                "guard t62 * h.a.value <= 1.0m else Ok\n    No", EXAMPLE));
    }

    @Test
    void theSameLineWithNoExampleToRunIt() {
        isAnsweredWithoutAnInternalError(model(squarings(62),
                "guard t62 * h.a.value <= 1.0m else Ok\n    No", ""));
    }

    @Test
    void theSameLineAsACondition() {
        isAnsweredWithoutAnInternalError(model(squarings(62),
                "if t62 * h.a.value <= 1.0m then Ok else No", ""));
    }

    @Test
    void aLineBeyondTheHostWithAnotherOnTheSameQuantityIsNotAnInternalError() {
        isAnsweredWithoutAnInternalError(model(squarings(62),
                "guard t62 * h.a.value <= 1.0m else Ok\n    guard h.a.value <= 1.0m else Ok\n    No",
                ""));
        isAnsweredWithoutAnInternalError(model(squarings(62),
                "guard h.a.value <= 1.0m else Ok\n    guard t62 * h.a.value <= 1.0m else Ok\n    No",
                ""));
    }
}
