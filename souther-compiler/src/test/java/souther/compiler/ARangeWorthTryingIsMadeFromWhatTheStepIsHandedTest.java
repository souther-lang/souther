package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The ranges a walk is checked against are made from what the step is handed as well as from the
 * seed (spec §invariant-discharge-reduction).
 *
 * <p>The proof reads what holds of everything the step is handed while checking that the step stays
 * inside a range, and nothing read it while deciding which ranges to check. So a product of elements
 * at or above nought, started at one, was owed: the range it stays in is {@code [0, +∞)}, which is
 * neither the seed, nor either direction opened from it, nor the seed joined with what the step
 * answers with nothing assumed. Nobody proposed it, so nothing could prove it.
 *
 * <p>What is added is a symmetry and not a rule about products. A walk carries its accumulator
 * through what it was handed, so where the answer runs is where the two together run — and the
 * candidates are guesses either way, each costing one check and proving nothing it cannot survive
 * ({@code InductiveBounds}).
 *
 * <p>The three ways a product is proved are three different layers of the reading, which is what
 * makes them worth writing down together.
 */
class ARangeWorthTryingIsMadeFromWhatTheStepIsHandedTest {

    private static final String TYPES = """
            module demo

            data U = Int
                invariant nonNeg = value >= 0

            data AtLeastOne = Int
                invariant one = value >= 1

            data Money = Int
                invariant nonNeg = value >= 0
            """;

    private static boolean owed(String expression) {
        Compiler.Compiled compiled = Compiler.compileWithWarnings(TYPES + "\n" + """
                behavior total : (xs: List<U>, ns: List<Int>, ones: List<AtLeastOne>) -> Money
                    constructs Money

                let total (xs, ns, ones) = Money(%s)
                """.formatted(expression));
        return compiled.warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
    }

    /** Elements at or above one: the seed opened upward already held this, and it held it before
     * anything was read of what the step is handed. */
    @Test
    void aProductOfElementsAtOrAboveOneIsProvedFromTheSeed() {
        assertFalse(owed("List.fold((acc, x) -> acc * x.value, 1, ones)"));
        assertFalse(owed("List.product(List.map(x -> x.value, ones))"));
    }

    /** Elements written on the line: what bounds them is what is written there, and the range it
     * proposes is the one the seed and those numbers make together. */
    @Test
    void aProductOfElementsWrittenOutIsProvedFromWhatIsWritten() {
        assertFalse(owed("List.fold((acc, x) -> acc * x, 1, [2, 3])"));
        assertFalse(owed("List.product([2, 3])"));
    }

    /** Elements at or above nought: the case this commit is for. A product of them started at one
     * never leaves {@code [0, +∞)}, and that range is the seed joined with what the elements
     * guarantee. */
    @Test
    void aProductOfElementsAtOrAboveNoughtIsProvedFromWhatTheStepIsHanded() {
        assertFalse(owed("List.fold((acc, x) -> acc * x.value, 1, xs)"));
        assertFalse(owed("List.product(List.map(x -> x.value, xs))"));
    }

    /** And a longer list of guesses proves nothing more than it should: a product over elements
     * nothing bounds is owed, and so is a step that leaves every range the seed and the elements
     * make. */
    @Test
    void aRangeNothingHoldsIsStillNotProved() {
        assertTrue(owed("List.fold((acc, x) -> acc * x, 1, ns)"));
        assertTrue(owed("List.product(ns)"));
        assertTrue(owed("List.fold((acc, x) -> acc - x.value, 0, xs)"),
                "a total that takes away from itself leaves every range made from a seed of nought"
                        + " and elements at or above it");
    }
}
