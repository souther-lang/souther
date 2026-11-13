package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A body may be as deep as a definition holds ({@code source-structural-complexity-is-bounded}), so
 * a chain of {@code let}s that each convert the one before is a source the language accepts, and
 * the comparison at its end is read in the time its length asks and not the time its square or
 * cube asks.
 */
class AChainOfCaseConversionsIsReadInTimeTest {

    private static final int DEPTH = 150;

    private static String chain(boolean alternating) {
        StringBuilder body = new StringBuilder("{\n");
        for (int i = 1; i <= DEPTH; i++) {
            body.append("  let a").append(i).append(" = String.")
                    .append(alternating && i % 2 == 0 ? "uppercase" : "lowercase").append("(")
                    .append(i == 1 ? "i" : "a" + (i - 1)).append(")\n");
        }
        body.append("  a").append(DEPTH).append(" == j\n}");
        return "module chain\n\nbehavior f : (i: String, j: String) -> Bool\n\nlet f (i, j) = "
                + body + "\n";
    }

    @Test
    void theComparisonAtTheEndIsReadWithinSecondsAndNotMinutes() {
        assertTimeoutPreemptively(Duration.ofSeconds(30), () -> ACompiledModel.measured(
                chain(false), Adequacy.Asked.warningsAt(Adequacy.Level.ALL)));
    }

    @Test
    void aChainThatAlternatesBetweenTheTwoIsReadWithinSecondsToo() {
        assertTimeoutPreemptively(Duration.ofSeconds(30), () -> ACompiledModel.measured(
                chain(true), Adequacy.Asked.warningsAt(Adequacy.Level.ALL)));
    }
}
