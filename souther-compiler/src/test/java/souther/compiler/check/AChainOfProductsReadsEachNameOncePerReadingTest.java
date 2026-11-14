package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.SequencedMap;

/**
 * A chain of {@code let}s that each multiply the one before by an input is read by many readings
 * (the comparison's, each factor's, each node's range), and each of them used to walk the names
 * below its node afresh, so the values of names read grew with the cube of the chain.
 *
 * <p>Held as how many values of names were read and folded, not as how long it takes: doubling the
 * chain leaves each at most four times and a bit, which is the square, where the cube is eight.
 * A chain of 300 is the same claim at a size that costs ten seconds, and nothing here needs it.
 */
class AChainOfProductsReadsEachNameOncePerReadingTest {

    private static final int[] LINKS = {20, 40, 80};

    /** The values of names read afresh for a form, and the values of names folded afresh. */
    private static long[] namesWorkedOut(int links) {
        StringBuilder body = new StringBuilder("{\n");
        for (int i = 1; i <= links; i++) {
            body.append("  let a").append(i).append(" = ")
                    .append(i == 1 ? "n" : "a" + (i - 1)).append(" * m\n");
        }
        body.append("  a").append(links).append(" == m\n}");
        String source = "module chain\n\nbehavior f : (n: Int, m: Int, s: String) -> Bool\n\n"
                + "let f (n, m, s) = " + body + "\n";
        long[] read = {0};
        long[] folded = {0};
        AffineForms.NAMES_READ = read;
        FoldedValue.FOLDED = folded;
        try {
            ACompiledModel.measured(source, Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        } finally {
            AffineForms.NAMES_READ = null;
            FoldedValue.FOLDED = null;
        }
        return new long[] {read[0], folded[0]};
    }

    @Test
    void doublingTheChainWorksOutNoMoreThanFourTimesAndABitTheNamesItReadsAndFolds() {
        SequencedMap<Integer, Long> read = new LinkedHashMap<>();
        SequencedMap<Integer, Long> folded = new LinkedHashMap<>();
        for (int links : LINKS) {
            long[] counted = namesWorkedOut(links);
            read.put(links, counted[0]);
            folded.put(links, counted[1]);
        }
        Growth.eachAtMost(read, 9, 2);
        Growth.eachAtMost(folded, 9, 2);
    }
}
