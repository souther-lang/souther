package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A chain of {@code let}s that each take the remainder of the one before added to itself is read in
 * the time its length asks and not in a time that doubles with every link.
 *
 * <p>The reason a remainder is no number is asked of the dividend, and the dividend names the one
 * before twice. A reading kept for a node is taken again where the reading would come to the same,
 * which includes where it is made inside a watch of what an application handed; if it is not kept
 * there, each of the two names asks the whole chain below it and the work is two to the power of
 * the depth. At this depth that is longer than anyone waits, and the bound is not near the time
 * the reading takes.
 */
class AChainOfRemaindersEachOverTheOneBeforeTwiceIsReadInTimeTest {

    private static final int DEPTH = 30;

    private static String chain(String comparison) {
        StringBuilder body = new StringBuilder("{\n    let a0 = p.x\n");
        for (int i = 1; i <= DEPTH; i++) {
            body.append("    let a").append(i).append(" = Int.floorMod(a").append(i - 1)
                    .append(" + a").append(i - 1).append(", 7)\n");
        }
        body.append("    a").append(DEPTH).append(' ').append(comparison).append(" p.j\n}");
        return "module chain\n\ndata Pair = { x: Int, j: Int }\n\n"
                + "behavior m : (p: Pair) -> Bool\n\nlet m (p) = " + body + "\n";
    }

    @Test
    void aChainComparedForEqualityIsReadWithinSecondsAndNotMinutes() {
        assertTimeoutPreemptively(Duration.ofSeconds(60), () -> ACompiledModel.measured(
                chain("=="), Adequacy.Asked.warningsAt(Adequacy.Level.ALL)));
    }

    @Test
    void aChainComparedForOrderIsReadWithinSecondsToo() {
        assertTimeoutPreemptively(Duration.ofSeconds(60), () -> ACompiledModel.measured(
                chain(">="), Adequacy.Asked.warningsAt(Adequacy.Level.ALL)));
    }
}
