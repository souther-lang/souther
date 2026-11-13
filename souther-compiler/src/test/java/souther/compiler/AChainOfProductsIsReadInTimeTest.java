package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A definition may be 320 deep ({@code source-structural-complexity-is-bounded}), so a chain of
 * {@code let}s that each multiply the one before by an input is a source the language accepts, and
 * the comparison at its end is read in the time its length asks and not the time its cube asks.
 */
class AChainOfProductsIsReadInTimeTest {

    private static final int DEPTH = 300;

    private static String chain() {
        StringBuilder body = new StringBuilder("{\n");
        for (int i = 1; i <= DEPTH; i++) {
            body.append("  let a").append(i).append(" = ")
                    .append(i == 1 ? "n" : "a" + (i - 1)).append(" * m\n");
        }
        body.append("  a").append(DEPTH).append(" == m\n}");
        return "module chain\n\nbehavior f : (n: Int, m: Int, s: String) -> Bool\n\n"
                + "let f (n, m, s) = " + body + "\n";
    }

    @Test
    void theComparisonAtTheEndIsReadWithinSecondsAndNotMinutes() {
        assertTimeoutPreemptively(Duration.ofSeconds(30), () -> ACompiledModel.measured(
                chain(), Adequacy.Asked.warningsAt(Adequacy.Level.ALL)));
    }
}
