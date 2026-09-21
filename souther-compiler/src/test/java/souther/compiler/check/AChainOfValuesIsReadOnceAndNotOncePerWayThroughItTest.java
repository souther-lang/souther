package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A value is held once for the analysis however many ways there are through the values that name
 * it, so a chain of them costs what it is long and not what it fans out to.
 *
 * <p>Each value here names the one before it in two forks, so the number of ways down the chain
 * doubles with every link. A tree that held a copy of a value for every region that builds it
 * would double with them, and the compile of forty links is not one anybody waits for. Held as a
 * time and not as a size: what the value being held once is for is that nothing scales with the
 * ways, and a tree that stopped growing but was still read once per way would pass a count.
 */
class AChainOfValuesIsReadOnceAndNotOncePerWayThroughItTest {

    private static final int LINKS = 80;

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
    void aLongChainIsCompiledInATimeAPersonWouldWait() {
        assertTimeoutPreemptively(Duration.ofSeconds(20),
                () -> assertDoesNotThrow(() -> Compiler.compile(diamonds(LINKS))));
    }
}
