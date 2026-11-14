package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a reading asked of the names handed is as large as the chain of {@code let}s under it, and
 * it is passed to the watch outside it each time a reading ends inside one and each time a reading
 * kept is taken again. Held there as the names looked at to place a set and the sets walked to ask
 * of one, and not as how long it takes.
 */
class AChainOfRemaindersPassesItsAskedNamesOnWithoutListingThemTest {

    private static final int[] LINKS = {40, 80, 160};

    private static long[] counted(int links) {
        StringBuilder body = new StringBuilder("{\n  let a0 = p.x\n");
        for (int i = 1; i <= links; i++) {
            body.append("  let a").append(i).append(" = Int.floorMod(a").append(i - 1)
                    .append(" + a").append(i - 1).append(", 7)\n");
        }
        body.append("  a").append(links).append(" == p.j\n}");
        String source = "module chain\n\ndata Pair = { x: Int, j: Int }\n\n"
                + "behavior f : (p: Pair) -> Bool\n\nlet f (p) = " + body + "\n";
        long[] counting = new long[3];
        AskedNames.COUNTING = counting;
        try {
            ACompiledModel.measured(source, Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        } finally {
            AskedNames.COUNTING = null;
        }
        return counting;
    }

    @Test
    void noNameIsLookedAtToPlaceASetAndNoSetIsWalkedWhereNothingWasHandedDifferently() {
        SequencedMap<Integer, Long> taken = new LinkedHashMap<>();
        for (int links : LINKS) {
            long[] counting = counted(links);
            assertEquals(0L, counting[0], "names looked at to place a set, at " + links);
            assertEquals(0L, counting[1], "sets walked to ask of one, at " + links);
            taken.put(links, counting[2]);
        }
        // What is counted is the sets taken in and not the names in them: doubling the chain
        // doubles the sets and a bit, where the names they held grew by more than the square.
        Growth.eachAtMost(taken, 4, 1);
    }
}
