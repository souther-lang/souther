package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.SequencedMap;

/**
 * A chain of {@code let}s that each take the remainder of the one before added to itself states a
 * truth for each link, and a reader is made for each truth. Each of them asks why the remainder
 * under its truth is no number of the input, which is asked of the dividend and so of the
 * remainder under that, and the same reason comes of every link of the chain.
 *
 * <p>A reading kept for the reader that made it is made again by every other reader: the chain is
 * read down to the bottom once for each truth, and the readings made grow with the square of its
 * length. Kept for the input, each is made once.
 *
 * <p>Held as how many remainders and reasons were read afresh, not as how long it takes: doubling
 * the chain leaves it at most twice and a bit, where the square is four. Over 20, 40 and 80 links
 * the readings made were 637, 2077 and 7357 where each reader kept its own, and 347, 707 and 1427
 * where the input does.
 */
class AChainOfRemaindersIsReadOncePerReadingForAllItsTruthsTest {

    private static final int[] LINKS = {20, 40, 80};

    private static long readingsMade(int links) {
        StringBuilder body = new StringBuilder("{\n  let a0 = p.x\n");
        for (int i = 1; i <= links; i++) {
            body.append("  let a").append(i).append(" = Int.floorMod(a").append(i - 1)
                    .append(" + a").append(i - 1).append(", 7)\n");
        }
        body.append("  a").append(links).append(" == p.j\n}");
        String source = "module chain\n\ndata Pair = { x: Int, j: Int }\n\n"
                + "behavior f : (p: Pair) -> Bool\n\nlet f (p) = " + body + "\n";
        long[] made = {0};
        Pullback.READINGS_MADE = made;
        try {
            ACompiledModel.measured(source, Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        } finally {
            Pullback.READINGS_MADE = null;
        }
        return made[0];
    }

    @Test
    void doublingTheChainMakesNoMoreThanTwiceAndABitTheReadingsOfRemaindersAndReasons() {
        SequencedMap<Integer, Long> made = new LinkedHashMap<>();
        for (int links : LINKS) {
            made.put(links, readingsMade(links));
        }
        Growth.eachAtMost(made, 5, 2);
    }
}
