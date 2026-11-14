package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.SequencedMap;

/**
 * A chain of {@code let}s that each take the remainder of the one before added to itself is read by
 * a reading for each link: the dividend of each remainder, as a form of the input's numbers. A
 * reading that keeps what a name came to for as long as it runs reads the chain below its link down
 * to the bottom, and the readings one for each link read the names of the chain as many times as
 * the square of its length.
 *
 * <p>Held as how many values of names were read afresh, not as how long it takes: doubling the chain
 * leaves it at most four times and a bit, which is the square, where the cube is eight. Doubling
 * from 20 to 80 links read 5.1 and 6.1 times as many where each walk started its own table, and 2.8
 * and 3.1 times as many where the owner of the reading holds them.
 */
class AChainOfRemaindersReadsEachNameOncePerReadingTest {

    private static final int[] LINKS = {20, 40, 80};

    private static long namesRead(int links) {
        StringBuilder body = new StringBuilder("{\n  let a0 = p.x\n");
        for (int i = 1; i <= links; i++) {
            body.append("  let a").append(i).append(" = Int.floorMod(a").append(i - 1)
                    .append(" + a").append(i - 1).append(", 7)\n");
        }
        body.append("  a").append(links).append(" == p.j\n}");
        String source = "module chain\n\ndata Pair = { x: Int, j: Int }\n\n"
                + "behavior f : (p: Pair) -> Bool\n\nlet f (p) = " + body + "\n";
        long[] read = {0};
        AffineForms.NAMES_READ = read;
        try {
            ACompiledModel.measured(source, Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        } finally {
            AffineForms.NAMES_READ = null;
        }
        return read[0];
    }

    @Test
    void doublingTheChainReadsNoMoreThanFourTimesAndABitTheNamesItReads() {
        SequencedMap<Integer, Long> read = new LinkedHashMap<>();
        for (int links : LINKS) {
            read.put(links, namesRead(links));
        }
        Growth.eachAtMost(read, 9, 2);
    }
}
