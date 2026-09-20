package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the analysis copies of a chain of values is bounded, so a chain that grows with each link is
 * refused when it has grown too far and not after it has been built.
 *
 * <p>The bound is a limit of how the reading an analysis makes is represented, and the tests hold
 * its behaviour rather than its number: a short chain is read, a chain that plainly grows past any
 * ordinary model is refused, and it is refused in a time a person would wait.
 */
class TheAnalysisOfAChainOfValuesIsBoundedTest {

    /** Each value names the one before it in two forks, so what the analysis copies of it doubles
     *  with every link. */
    private static String diamonds(int links) {
        StringBuilder source = new StringBuilder(
                "module m exposing (f)\n\nlet a0 = List.length([1, 2, 3]) > 2\n");
        for (int i = 1; i <= links; i++) {
            String previous = "a" + (i - 1);
            source.append("let a").append(i).append(" = (if List.length([1]) > 0 then ")
                    .append(previous).append(" else false) || (if List.length([1, 2]) > 1 then ")
                    .append(previous).append(" else false)\n");
        }
        return source.append("\nbehavior f : (n: Int) -> Bool\nlet f (n) = a")
                .append(links).append('\n').toString();
    }

    @Test
    void aShortChainIsRead() {
        assertDoesNotThrow(() -> Compiler.compile(diamonds(4)));
    }

    @Test
    void aChainThatGrowsWithEveryLinkIsRefusedQuickly() {
        CompileException refused = assertTimeoutPreemptively(Duration.ofSeconds(10),
                () -> assertThrows(CompileException.class,
                        () -> Compiler.compile(diamonds(40))));

        assertTrue(refused.getMessage().contains("E2107"), refused.getMessage());
    }
}
