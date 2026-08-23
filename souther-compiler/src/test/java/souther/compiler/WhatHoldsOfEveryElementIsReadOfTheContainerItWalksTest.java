package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reduction may assume of the element it is handed is read of the container it walks
 * (spec §invariant-discharge-reduction).
 *
 * <p>It used to be read of the element's own type and of the line the container was written on, and
 * those are two of the things a container says — they are not the container. So a walk over a list a
 * {@code List.map} had built knew nothing of its elements, however much was known of the elements
 * they were built from and however plainly the closure said which place of them it answered: the
 * facts were held against the binder the producer was written with, and the consumer had never met
 * it. Eleven totals in one model were rewritten to avoid it.
 *
 * <p>So the reading is of the container expression, by the path under an element each bound is about
 * ({@code UniversalElementFacts}), and the fold instantiates those paths at the place its element
 * arrives. Every case here is one walk written two ways, or one walk over two containers that hold
 * the same elements — and the neighbours that stay reported are what says the reading is of the
 * elements rather than of the shape of the tree.
 */
class WhatHoldsOfEveryElementIsReadOfTheContainerItWalksTest {

    private static final String TYPES = """
            module demo

            data U = Int
                invariant nonNeg = value >= 0

            data Money = Int
                invariant nonNeg = value >= 0

            let over (n: Int): Bool = n > 1
            """;

    private static boolean owed(String expression) {
        Compiler.Compiled compiled = Compiler.compileWithWarnings(TYPES + "\n" + """
                behavior total : (xs: List<U>, ns: List<Int>) -> Money
                    constructs Money

                let total (xs, ns) = Money(%s)
                """.formatted(expression));
        return compiled.warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
    }

    /** The walk the fix is about: the same total, written as a fold over the elements and as a fold
     * over a list mapped from them. Neither is more true than the other. */
    @Test
    void aFoldOverWhatAMapBuiltReadsWhatTheMappedPlaceGuaranteed() {
        assertFalse(owed("List.fold((acc, x) -> acc + x.value, 0, xs)"),
                "the element's own type says its carrier is at or above nought");
        assertFalse(owed("List.fold((acc, x) -> acc + x, 0, List.map(x -> x.value, xs))"),
                "and the list mapped from that place holds the same numbers");
    }

    /** The reading travels as far as the container was built through: what was kept of a list is
     * kept of a list built from that one. */
    @Test
    void whatWasKeptTravelsThroughEveryConstructionThatKeptIt() {
        assertFalse(owed("List.fold((acc, x) -> acc + x, 0, List.map(x -> x.value, List.reverse(xs)))"),
                "the same elements in another order are the same elements, and the map reads the"
                        + " same place of each of them");
    }

    /** A closure that computes rather than reads answers something this says nothing of, and the
     * walk is reported — which is what says the mapped case carries what a place guaranteed and not
     * whatever the closure was written with. */
    @Test
    void aClosureThatComputesItsAnswerCarriesNothing() {
        assertTrue(owed("List.fold((acc, x) -> acc + x, 0, List.map(x -> x.value - 1, xs))"),
                "one less than a number at or above nought is a number this is told nothing about");
    }

    /**
     * A container written out bounds its elements, and goes on bounding them through a construction
     * that kept them.
     *
     * <p>The written-out elements were read of the container the walk was handed and of nothing
     * else, so {@code [1, 2, 3]} bounded a fold and {@code List.reverse([1, 2, 3])} bounded none.
     */
    @Test
    void elementsWrittenOutBoundAWalkThroughWhatKeepsThem() {
        assertFalse(owed("List.fold((acc, x) -> acc + x, 0, [1, 2, 3])"));
        assertFalse(owed("List.fold((acc, x) -> acc + x, 0, List.reverse([1, 2, 3]))"),
                "the same three numbers in another order");
        assertFalse(owed("List.fold((acc, x) -> acc + x, 0, List.filter(x -> over(x), [1, 2, 3]))"),
                "some of the same three numbers, and nothing else is there");
        assertFalse(owed("List.fold((acc, x) -> acc + x, 0, List.map(x -> x, [1, 2, 3]))"),
                "each of them answered as it stands");
    }

    /** The neighbour that stays reported: a list of numbers nothing bounds is one nothing bounds,
     * however it is written. */
    @Test
    void aContainerThatGuaranteesNothingBoundsNothing() {
        assertTrue(owed("List.fold((acc, x) -> acc + x, 0, ns)"));
        assertTrue(owed("List.fold((acc, x) -> acc + x, 0, List.reverse(ns))"));
        assertTrue(owed("List.fold((acc, x) -> acc + x, 0, List.map(x -> x, ns))"));
    }

    /** And what a walk over a list ordered or thinned reads is what it read before this was written:
     * both were already answered by the element's own type, and moving where the answer comes from
     * left them where they were. */
    @Test
    void aWalkOverAListOrderedOrThinnedReadsWhatItAlwaysRead() {
        assertFalse(owed("List.fold((acc, x) -> acc + x.value, 0, List.reverse(xs))"));
        assertFalse(owed("List.fold((acc, x) -> acc + x.value, 0, List.filter(x -> over(x.value), xs))"));
    }
}
