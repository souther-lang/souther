package souther.compiler.cst;

import org.junit.jupiter.api.Test;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.SequencedMap;

/**
 * A nest is walked, not rescanned. The lambda lookahead reads the parenthesised run at every level
 * of one, and deriving each token position from the cursor again made that cost the cube of the
 * depth.
 *
 * <p>What is counted is the tokens the parser looks at over one parse, at three depths each double
 * the last. A lookahead that walks the run once per level looks at the square of the depth, which
 * is four times as many tokens for twice the depth; one that finds each token from the cursor again
 * looks at the cube, which is eight times as many.
 */
class ANestOfParenthesesIsWalkedNotRescannedAtEveryLevelTest {

    private static long lookedAtFor(int depth) {
        String source = "module m\n\nlet f = " + "(".repeat(depth) + "1" + ")".repeat(depth) + "\n";
        long[] counting = {0};
        CstParser.COUNTING_LOOKED_AT = counting;
        try {
            CstParser.parse(source);
        } finally {
            CstParser.COUNTING_LOOKED_AT = null;
        }
        return counting[0];
    }

    @Test
    void doublingTheDepthAtMostQuadruplesWhatTheParserLooksAt() {
        SequencedMap<Integer, Long> lookedAt = new LinkedHashMap<>();
        for (int depth : new int[] {16, 32, 64}) {
            lookedAt.put(depth, lookedAtFor(depth));
        }
        Growth.eachAtMost(lookedAt, 9, 2);
    }
}
