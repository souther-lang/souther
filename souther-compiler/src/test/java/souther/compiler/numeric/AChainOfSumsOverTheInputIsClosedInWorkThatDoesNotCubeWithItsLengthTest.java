package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A chain of {@code let}s that each add to the one before, compared with a bound on the input, is
 * closed in work that grows with the square of its length and not with its cube.
 *
 * <p>Every link is one more rule over the same two numbers, and every link's closure is asked, for
 * each form its rules weigh, whether the rules leave it a value. That is as many forms as rules, and
 * read against every premise it is the square of the rules for each closure and the cube over the
 * chain: twice the links cost eight times the premises read. The premises are read once each into an
 * index and each form is asked of the index, which is the work held here — counted and not timed,
 * since a count is a shape and a time is a machine.
 *
 * <p>Both shapes are held: each link adds the one before to itself and to the input, so that what
 * it weighs doubles, or adds the input alone, so that what it weighs grows by one.
 */
class AChainOfSumsOverTheInputIsClosedInWorkThatDoesNotCubeWithItsLengthTest {

    private static String chain(int links, boolean doubling) {
        StringBuilder body = new StringBuilder("{\n    let a0 = p.x\n");
        for (int i = 1; i <= links; i++) {
            body.append("    let a").append(i).append(" = a").append(i - 1);
            if (doubling) {
                body.append(" + a").append(i - 1);
            }
            body.append(" + p.j\n");
        }
        body.append("    a").append(links).append(" >= p.j\n}");
        return "module chain\n\ndata Pair = { x: Int, j: Int }\n\n"
                + "behavior m : (p: Pair) -> Bool\n\nlet m (p) = " + body + "\n";
    }

    /** The premises read and the questions asked of an index, while the chain is measured. */
    private static long workClosing(int links, boolean doubling) {
        long premises = ClosedState.premisesWorked();
        long steps = ReachIndex.steps();
        ACompiledModel.measured(chain(links, doubling),
                Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        return (ClosedState.premisesWorked() - premises) + (ReachIndex.steps() - steps);
    }

    @Test
    void twiceTheLinksCostLessThanFiveTimesTheWorkWhetherTheChainDoublesOrAddsOne() {
        for (boolean doubling : new boolean[] {true, false}) {
            long shorter = workClosing(16, doubling);
            long longer = workClosing(32, doubling);
            assertTrue(shorter > 0, "nothing was counted, so this holds nothing");
            // The square is four times and the cube eight; closing every link in work that reads
            // every premise for every form is the cube.
            assertTrue(longer < 5 * shorter, "twice the links cost " + longer
                    + " where the shorter chain cost " + shorter
                    + (doubling ? ", doubling" : ", adding one"));
        }
    }
}
