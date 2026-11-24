package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.ClosedState;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.AGuardThatAValueIsNotInASetIsReadByWhatAnInsertOfItAnswersTest.warnings;

/**
 * A chain {@code a_k = a_(k-1) * a_(k-1) + a_(k-1)} ending in a guard is read in time that grows
 * with the length of the chain and not with the pairs of its links.
 *
 * <p>Every link states a bound on the sum of the links before it beside a bound on its own product.
 * Read over the products, each sum names every product before it, and a reading that asks what the
 * rest of a sum leaves has a premise to look at for each of them, for each of the sums: the cube of
 * the length. Read over the running sums, which is what the rules are closed in, each rule is a
 * bound on one position or on a difference, and no rule is read against another at all. Counted
 * rather than timed: that is a shape, and how long it takes is the machine's.
 *
 * <p>What the guard comes to is held beside it: the chain is read the same at every length, since
 * a reading that gave up speed and kept the answer is one thing and a reading that changed the
 * answer is another.
 */
class AChainOfSumsOverProductsIsClosedWithoutReadingARuleAgainstAnotherTest {

    private static String chain(int depth) {
        StringBuilder out = new StringBuilder();
        out.append("module probe.chain\n\ndata Pair = { x: Int, j: Int }\n\n");
        out.append("behavior m : (p: Pair) -> Bool\nlet m (p) = {\n    let a0 = p.x\n");
        for (int at = 1; at <= depth; at++) {
            out.append("    let a").append(at).append(" = a").append(at - 1).append(" * a")
                    .append(at - 1).append(" + a").append(at - 1).append('\n');
        }
        out.append("    a").append(depth).append(" >= p.j\n}\n");
        return out.toString();
    }

    private static long premisesWorkedReading(String source) {
        long before = ClosedState.premisesWorked();
        warnings(source);
        return ClosedState.premisesWorked() - before;
    }

    @Test
    void premisesLookedAtGrowWithTheLengthOfTheChain() {
        long shallow = premisesWorkedReading(chain(8));
        long twiceAsDeep = premisesWorkedReading(chain(16));
        long fourTimesAsDeep = premisesWorkedReading(chain(32));
        // Read over the products the counts were cubic, which is eight times as many at twice the
        // depth. Over the running sums they are not read against one another, so what is left of
        // them is the quadratic of the questions about each sum one at a time.
        assertTrue(twiceAsDeep < 5 * shallow + 1000, "depth 16 looked at " + twiceAsDeep
                + " premises where depth 8 looked at " + shallow);
        assertTrue(fourTimesAsDeep < 5 * twiceAsDeep + 1000, "depth 32 looked at " + fourTimesAsDeep
                + " premises where depth 16 looked at " + twiceAsDeep);
    }

    @Test
    void theGuardIsReadTheSameAtEveryLength() {
        List<String> shallow = warnings(chain(4));
        assertEquals(shallow, warnings(chain(8)));
        assertEquals(shallow, warnings(chain(16)));
    }
}
