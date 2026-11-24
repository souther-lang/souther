package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.SequencedMap;

/**
 * A value is held once for the analysis however many ways there are through the values that name
 * it, so a chain of them costs what it is long and not what it fans out to.
 *
 * <p>Each value here names the one before it in two forks, so the number of ways down the chain
 * doubles with every link. A tree that held a copy of a value for every region that builds it
 * would double with them, and the compile of forty links is not one anybody waits for. A tree that
 * stopped growing but was still read once per way would pass a count of its size, so what is
 * counted is the nodes the compile names and the walks it starts: doubling the chain may at most
 * double them, where one reading per way squares them.
 */
class AChainOfValuesIsReadOnceAndNotOncePerWayThroughItTest {

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

    /** What compiling a chain of {@code links} names and the walks it starts, as one count. */
    private static long readsOver(int links) {
        long[] named = {0};
        long[] walks = {0};
        Terms.COUNTING_NAMED = named;
        Terms.COUNTING_WALKS = walks;
        try {
            Compiler.compile(diamonds(links));
        } finally {
            Terms.COUNTING_NAMED = null;
            Terms.COUNTING_WALKS = null;
        }
        return named[0] + walks[0];
    }

    @Test
    void doublingTheChainAtMostDoublesWhatIsRead() {
        SequencedMap<Integer, Long> reads = new LinkedHashMap<>();
        for (int links : new int[] {3, 6, 12}) {
            reads.put(links, readsOver(links));
        }
        Growth.eachAtMost(reads, 3, 1);
    }
}
