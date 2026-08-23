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
        return owedIn("let total (xs, ns) = Money(%s)".formatted(expression));
    }

    /** The same total, with the container bound to a name first. */
    private static boolean owedWhereTheContainerIsNamed(String container, String walk) {
        return owedIn("""
                let total (xs, ns) = {
                    let ys = %s
                    Money(%s)
                }""".formatted(container, walk));
    }

    private static boolean owedIn(String body) {
        return owedInModule(body.startsWith("module ") ? body : TYPES + "\n" + """
                behavior total : (xs: List<U>, ns: List<Int>) -> Money
                    constructs Money

                %s
                """.formatted(body));
    }

    private static boolean owedInModule(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
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

    /**
     * What a closure answered is read from what it was applied to.
     *
     * <p>Not a projection of the paths. A closure that reads a place hands on what was true there,
     * and one that computes hands on what the arithmetic makes of it — {@code x -> 0} answers nought
     * whatever it was handed, and one more than a number at or above nought is at or above one. Both
     * are the same question asked of the reading that owns it, on a domain holding the facts every
     * element satisfies and nothing else.
     */
    @Test
    void whatAClosureAnsweredIsReadFromWhatItWasAppliedTo() {
        assertFalse(owed("List.fold((acc, x) -> acc + x, 0, List.map(x -> 0, xs))"),
                "nought, whatever the element was");
        assertFalse(owed("List.fold((acc, x) -> acc + x, 0, List.map(x -> x.value + 1, xs))"),
                "one more than a number at or above nought");
        assertTrue(owed("List.fold((acc, x) -> acc + x, 0, List.map(x -> x.value - 1, xs))"),
                "and one less than one may be below nought, so the total may be");
    }

    /**
     * An element that is one of two things is bounded by both.
     *
     * <p>{@code Map.updateIfPresent} answers the map it was given with one value replaced, and its
     * rule used to say every value was the closure's answer. Read that way beside a closure that
     * raises what it was handed, the values that were already there would be credited with what the
     * closure promised and were never given to it. So the two are held apart here: the same closure
     * through {@code Map.mapValues}, which does answer every value, proves the product; through
     * {@code Map.updateIfPresent} it does not.
     */
    @Test
    void anElementThatIsOneOfTwoThingsIsBoundedByBoth() {
        String product = """
                module demo

                data U = Int
                    invariant nonNeg = value >= 0

                data AtLeastOne = Int
                    invariant one = value >= 1

                behavior total : (m: Map<String, U>) -> AtLeastOne
                    constructs AtLeastOne, U
                let total (m) = AtLeastOne(Map.fold((acc, k, v) -> acc * v.value, 1, %s))
                """;
        assertFalse(owedIn(product.formatted("Map.mapValues((k, v) -> U(v.value + 1), m)")),
                "every value of a mapped map is what the closure answered, which is at or above one");
        assertTrue(owedIn(product.formatted("Map.updateIfPresent(\"a\", v -> U(v.value + 1), m)")),
                "a value the closure never saw is the one that was there, which may be nought");
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

    /**
     * A container bound to a name is the container it was given.
     *
     * <p>The name was followed for the elements a container is written out with and not for what a
     * construction kept, so a total written in one line was read and the same total with its list
     * given a name was not. Two answers to "which container is this", inside the one reading written
     * to stop a fact depending on how it was spelled.
     */
    @Test
    void aContainerGivenANameIsTheContainerItWasGiven() {
        assertFalse(owedWhereTheContainerIsNamed(
                "List.map(x -> x.value, xs)", "List.fold((acc, x) -> acc + x, 0, ys)"));
        assertFalse(owedWhereTheContainerIsNamed(
                "List.reverse([1, 2, 3])", "List.fold((acc, x) -> acc + x, 0, ys)"));
        assertTrue(owedWhereTheContainerIsNamed(
                "List.map(x -> x, ns)", "List.fold((acc, x) -> acc + x, 0, ys)"),
                "and a name given to a list nothing bounds bounds nothing");
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
