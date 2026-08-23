package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a value carries by being what it is, read where a step is read as well as where a path is
 * (#988).
 *
 * <p>A size is never negative and an absolute value is not, whatever any condition said and whatever
 * declaration was written. Those hold of the value, so they hold on every arm of every choice and
 * before any guard — and they were collected by walking the expression a reading had, which meant a
 * reduction's step, read out of forms and atoms, had none of them. What that came to is the pair
 * below: one fold discharged and its neighbour did not, differing in nothing but which of two
 * spellings of one guard the author wrote.
 *
 * <p>Both sides of the boundary are here. Everything written on a path was already silent and stays
 * silent, which is what says the change was not to the rules; and every row that a fact is not
 * enough for stays reported, which is what says the facts are being used rather than assumed past.
 */
class WhatAValueCarriesReachesAStepAsItReachesAPathTest {

    private static final String TYPES = """
            module demo

            data Positive = Int
                invariant atLeastOne = value >= 1

            data AtLeastTwo = Int
                invariant twoUp = value >= 2

            data NonNegD = Decimal
                invariant nn = value >= 0.0m

            data Counted =
                { items: List<Int>
                }
            """;

    private static boolean owed(String body) {
        return Compiler.compileWithWarnings(TYPES + "\n" + body).warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
    }

    /**
     * The pair the issue was written from: one guard, two spellings, one value, one bound needed.
     *
     * <p>The comparison states {@code length > 0} on its own, which is a relation a condition wrote
     * and stands beside the arm. The emptiness check normalises to {@code length /= 0}, and "not
     * nought" bounds nothing without "never below nought" — which no condition said and no
     * declaration writes, being what a length is.
     */
    @Test
    void twoSpellingsOfOneGuardAnswerAlikeInsideAFold() {
        assertFalse(owed("""
                behavior total : (xs: List<Counted>) -> Positive
                    constructs Positive

                let total (xs) = Positive(List.fold(
                    (a, c) -> if List.length(c.items) > 0 then a + List.length(c.items) else a,
                    1, xs))
                """), "the guard states the bound itself");
        assertFalse(owed("""
                behavior total : (xs: List<Counted>) -> Positive
                    constructs Positive

                let total (xs) = Positive(List.fold(
                    (a, c) -> if Bool.not(List.isEmpty(c.items)) then a + List.length(c.items) else a,
                    1, xs))
                """), "and the emptiness check leaves the bound to what a length is");
    }

    /**
     * And with no guard at all, which is what says this is not about conditions.
     *
     * <p>The row that rules out recording these beside the arm a choice was decided by: there is no
     * choice here to record them beside.
     */
    @Test
    void aStepThatNamesASizeUnderNoGuardIsBoundedByWhatASizeIs() {
        assertFalse(owed("""
                behavior total : (xs: List<Counted>) -> Positive
                    constructs Positive

                let total (xs) = Positive(List.fold((a, c) -> a + List.length(c.items), 1, xs))
                """), "one plus something at or above nought is at or above one");
    }

    /** What an operation guarantees of its answer reaches a step the same way a size does. Two
     * sources in one family, and a reading that had one without the other would be answering by
     * which table a fact happened to be written in. */
    @Test
    void aStepThatNamesAnOperationsOwnGuaranteeIsBoundedByIt() {
        assertFalse(owed("""
                behavior total : (xs: List<Int>) -> Positive
                    constructs Positive

                let total (xs) = Positive(List.fold((a, x) -> a + Int.abs(x), 1, xs))
                """), "an absolute value is not negative, whatever the element is");
    }

    /** And through a recipe standing over it, since what a product is read from is where its
     * factors' own facts have to arrive. */
    @Test
    void aFactReachesAStepThroughTheArithmeticOverIt() {
        assertFalse(owed("""
                behavior total : (xs: List<Counted>) -> Positive
                    constructs Positive

                let total (xs) = Positive(List.fold((a, c) -> a + List.length(c.items) * 2, 1, xs))
                """), "twice something at or above nought is at or above nought");
    }

    /**
     * And the other way about: what a value carries reaching the arithmetic under it.
     *
     * <p>The two kinds of edge are one graph and a reading has to walk both ways along it.
     * {@code Decimal.toInt} carries that its answer is within one of what it rounded, and what it
     * rounded is a product here — so the answer is at or above nought only once the product is, and
     * the product is a recipe somebody has to put through this reading. Read where a clause names
     * it, the product is in the domain and is derived. Read inside a step, the step names the answer
     * and never the product, and a reading that derived only what the step named left it unbounded
     * — the same divergence as the rows above, along the edge they do not use.
     */
    @Test
    void whatAValueCarriesReachesTheArithmeticUnderIt() {
        assertFalse(owed("""
                behavior one : (d: NonNegD) -> Positive
                    constructs Positive

                let one (d) = Positive(Decimal.toInt(HALF_UP, d.value * d.value) + 1)
                """), "on a path");
        assertFalse(owed("""
                behavior total : (xs: List<NonNegD>) -> Positive
                    constructs Positive

                let total (xs) = Positive(List.fold(
                    (a, d) -> a + Decimal.toInt(HALF_UP, d.value * d.value), 1, xs))
                """), "and inside a step, where the step names the answer and not what it rounded");
    }

    /**
     * The same facts where they were already read, which is every writing on a path.
     *
     * <p>Silent before this and silent after. A change that made a step read what a path reads could
     * as easily have been a change to what either reads, and these are what say it was not.
     */
    @Test
    void whatIsWrittenOnAPathAnswersAsItDid() {
        assertFalse(owed("""
                behavior one : (c: Counted) -> Positive
                    constructs Positive

                let one (c) = Positive(List.length(c.items) + 1)
                """), "a size on the path");
        assertFalse(owed("""
                behavior one : (x: Int) -> Positive
                    constructs Positive

                let one (x) = Positive(Int.abs(x) + 1)
                """), "an operation's own guarantee on the path");
        assertFalse(owed("""
                behavior one : (c: Counted) -> Positive
                    constructs Positive

                let one (c) =
                    Positive(if Bool.not(List.isEmpty(c.items)) then List.length(c.items) else 1)
                """), "and a choice read on the path, under the spelling that states the least");
    }

    /**
     * A fact is what it is and no more.
     *
     * <p>Every silent row above has a neighbour here differing in one thing, so what discharged them
     * was the fact and not a reading that stopped asking. A size at or above nought does not put a
     * total above one; and it says nothing at all about what is left when it is taken away.
     */
    @Test
    void whatTheFactDoesNotReachStaysReported() {
        assertTrue(owed("""
                behavior total : (xs: List<Int>) -> AtLeastTwo
                    constructs AtLeastTwo

                let total (xs) = AtLeastTwo(List.fold((a, x) -> a + Int.abs(x), 1, xs))
                """), "at or above nought carries a seed of one to one, and not to two");
        assertTrue(owed("""
                behavior total : (xs: List<Counted>) -> Positive
                    constructs Positive

                let total (xs) = Positive(List.fold((a, c) -> a - List.length(c.items), 1, xs))
                """), "how far below one it goes is what a size has no upper end for");
        assertTrue(owed("""
                behavior total : (xs: List<Int>) -> Positive
                    constructs Positive

                let total (xs) = Positive(List.fold((a, x) -> a + x, 1, xs))
                """), "and an element nothing bounds is bounded by nothing here");
    }
}
