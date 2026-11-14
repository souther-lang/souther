package souther.compiler.check;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.function.LongSupplier;
import org.junit.jupiter.api.Test;
import souther.compiler.numeric.ClosedState;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

/**
 * A chain of names, each over a product or a remainder of the one before and the one before added to
 * it, is read in work that grows with the square of its depth and not with the cube.
 *
 * <p>Held by what is read and not by how long it takes, which is the machine's: how many positions
 * of a rule a basis was made from, and how many facts were taken into a reading. A path through the
 * chain has a closure at every place it gets to and a reading at every operation, and each of them
 * holds the rules or the forms said so far. Made again from every one of them, the positions read
 * between all the places are the cube of the depth, so twice the depth is eight times as many; made
 * from the one before, and from what a form asks that another form asked, only what is added is
 * read, and twice the depth is four times as many. The bound sits between the two.
 */
class AChainOfNamesOverAProductOrARemainderIsReadInWorkThatGrowsWithTheSquareOfItsDepthTest {

    private static final int SHALLOW = 12;
    private static final int TWICE_AS_DEEP = 24;

    /** More than the square allows for what a path adds beside the chain, and well under the cube. */
    private static final double BOUND = 5.5;

    private static String chain(int depth, boolean remainder) {
        StringBuilder out = new StringBuilder();
        out.append("module probe.chain\n\ndata Pair = { x: Int, j: Int }\n\n");
        out.append("behavior m : (p: Pair) -> Bool\nlet m (p) = {\n    let a0 = p.x\n");
        for (int i = 1; i <= depth; i++) {
            if (remainder) {
                out.append("    let a").append(i).append(" = Int.floorMod(a").append(i - 1)
                        .append(", 7) + a").append(i - 1).append('\n');
            } else {
                out.append("    let a").append(i).append(" = a").append(i - 1).append(" * a")
                        .append(i - 1).append(" + a").append(i - 1).append('\n');
            }
        }
        out.append("    a").append(depth).append(" >= p.j\n}\n");
        return out.toString();
    }

    private static long counted(LongSupplier counter, String source) {
        long before = counter.getAsLong();
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return counter.getAsLong() - before;
    }

    private static void assertGrowsNoFasterThanTheSquareAndABit(LongSupplier counter, String what,
                                                                boolean... remainders) {
        for (boolean remainder : remainders) {
            long shallow = counted(counter, chain(SHALLOW, remainder));
            long twiceAsDeep = counted(counter, chain(TWICE_AS_DEEP, remainder));
            assertTrue(shallow > 0, what + " were counted for none of a chain " + SHALLOW + " deep");
            assertTrue(twiceAsDeep < BOUND * shallow, "a chain " + TWICE_AS_DEEP + " deep"
                    + (remainder ? " over remainders" : " over products") + " read " + twiceAsDeep
                    + " " + what + " where one " + SHALLOW + " deep read " + shallow
                    + ", which is more than the square of the depth allows");
        }
    }

    @Test
    void thePositionsOfARuleABasisIsMadeFromAreReadOnceForEachRuleSaid() {
        assertGrowsNoFasterThanTheSquareAndABit(ClosedState::basisTermsRead,
                "positions of a rule", false, true);
    }

    /**
     * A basis made for a chain of names is closed along the chain, which an {@code Int} with its ends
     * in every rule is bounds for. Closed by every pair of coordinates it is the same answer at the
     * square of the length of the chain for each closure, which is the cube between them.
     */
    @Test
    void aBasisMadeForAChainOfNamesIsClosedAlongTheChain() {
        for (boolean remainder : new boolean[] {false, true}) {
            long before = ClosedState.basesClosedByEveryPair();
            counted(ClosedState::basisTermsRead, chain(TWICE_AS_DEEP, remainder));
            assertEquals(0, ClosedState.basesClosedByEveryPair() - before,
                    "a chain" + (remainder ? " over remainders" : " over products")
                            + " had a basis closed by every pair");
        }
    }

    /** Only a chain over products has values nothing bounds outside the affine fragment to derive
     *  the bounds of; one over remainders is read through the rules. */
    @Test
    void theFactsTakenIntoAReadingAreTakenOnceForEachFormThatAsksForThem() {
        assertGrowsNoFasterThanTheSquareAndABit(DerivedNumericFacts::factsTaken, "facts", false);
    }
}
