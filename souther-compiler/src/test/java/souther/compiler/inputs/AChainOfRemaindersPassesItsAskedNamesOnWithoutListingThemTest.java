package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reading asked of the names handed is as large as the chain of {@code let}s under it, and
 * it is passed to the watch outside it each time a reading ends inside one and each time a reading
 * kept is taken again. In a chain nothing is handed again, so none of it is written out: no name is
 * handled to work a set out and no step is walked up the applications.
 *
 * <p>One chain, long enough that a set written out for each reading it passes through is hundreds
 * of thousands of names; how the counts grow with the chain is not what is held.
 */
class AChainOfRemaindersPassesItsAskedNamesOnWithoutListingThemTest {

    private static final int LINKS = 20;

    @Test
    void noNameIsHandledToWorkASetOutWhereNothingWasHandedAgain() {
        StringBuilder body = new StringBuilder("{\n  let a0 = p.x\n");
        for (int i = 1; i <= LINKS; i++) {
            body.append("  let a").append(i).append(" = Int.floorMod(a").append(i - 1)
                    .append(" + a").append(i - 1).append(", 7)\n");
        }
        body.append("  a").append(LINKS).append(" == p.j\n}");
        String source = "module chain\n\ndata Pair = { x: Int, j: Int }\n\n"
                + "behavior f : (p: Pair) -> Bool\n\nlet f (p) = " + body + "\n";
        long[] counting = new long[4];
        AskedNames.COUNTING = counting;
        try {
            ACompiledModel.measured(source, Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        } finally {
            AskedNames.COUNTING = null;
        }

        assertTrue(counting[2] > 0, "sets were taken in, or this counts nothing");
        assertEquals(0L, counting[0], "names handled to work a set out");
        assertEquals(0L, counting[3], "steps walked up the applications");
    }
}
