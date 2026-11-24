package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rules prove only once they are written over the positions their equalities leave free is
 * proved by {@link NumericDomain#entails}, and is no part of what the ranges and the closed
 * differences say. And where the reduction alone finds the rules leave nothing, the path is not
 * unreachable: that is for the rules as they stand to say, so no goal is proved and none refuted.
 */
class WhatOnlyTheReducedRulesProveIsProvedAndAnEmptyReductionIsNotAnUnreachablePathTest {

    private static LinearForm<String> atom(String name) {
        return LinearForm.atom(name);
    }

    private static LinearForm<String> constant(long value) {
        return LinearForm.constant(ExactRatio.of(value));
    }

    private static LinearForm<String> sum(LinearForm<String> left, LinearForm<String> right) {
        return left.plus(right).orNull();
    }

    private static LinearForm<String> difference(LinearForm<String> left, LinearForm<String> right) {
        return left.minus(right).orNull();
    }

    private static Map<String, NumberSpace> spaces(Granularity granularity, String... atoms) {
        Map<String, NumberSpace> out = new LinkedHashMap<>();
        for (String each : atoms) {
            out.put(each, NumberSpace.spacedOnly(granularity));
        }
        return out;
    }

    private static NumericDomain<String> top() {
        return NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
    }

    /** {@code x = a + b} beside {@code y = b + a}: each rule alone says nothing of {@code x - y}. */
    @Test
    void twoEqualitiesTogetherProveWhatNeitherDoesAndTheRangesDoNotSayIt() {
        Map<String, NumberSpace> spaces = spaces(Granularity.DISCRETE, "a", "b", "x", "y");
        NumericDomain<String> domain = top()
                .assume(difference(atom("x"), sum(atom("a"), atom("b"))), Rel.EQ, spaces)
                .assume(difference(atom("y"), sum(atom("b"), atom("a"))), Rel.EQ, spaces);
        LinearForm<String> xLessY = difference(atom("x"), atom("y"));

        assertTrue(domain.entails(xLessY, Rel.LE));
        assertTrue(domain.entails(xLessY, Rel.GE));
        assertFalse(domain.provenByTheBoxAndItsDifferences(xLessY, Rel.LE),
                "what the closure holds is not changed by the reduction");
        assertFalse(domain.isBottom());
    }

    /**
     * {@code x = a + b}, {@code y = a + b} and {@code x + y < 2a + 2b} have no solution. The rules as
     * they stand do not show it, and the reduction alone does ({@code 0 < 0}); that is not a path
     * nobody reaches, so no goal follows from it and none is refuted.
     */
    @Test
    void whereOnlyTheReductionFindsNothingLeftNoGoalIsProvedAndNoneRefuted() {
        Map<String, NumberSpace> spaces = spaces(Granularity.DISCRETE, "a", "b", "x", "y");
        LinearForm<String> ab = sum(atom("a"), atom("b"));
        NumericDomain<String> domain = top()
                .assume(difference(atom("x"), ab), Rel.EQ, spaces)
                .assume(difference(atom("y"), ab), Rel.EQ, spaces)
                .assume(difference(sum(atom("x"), atom("y")),
                        ab.times(ExactRatio.of(2)).orNull()), Rel.LT, spaces);
        LinearForm<String> aAtLeast100 = difference(atom("a"), constant(100));
        LinearForm<String> aAtMostMinus100 = sum(atom("a"), constant(100));

        assertFalse(domain.isBottom(), "the rules as they stand leave something");
        assertFalse(domain.entails(aAtLeast100, Rel.GE));
        assertFalse(domain.entails(aAtMostMinus100, Rel.LE));
        assertFalse(domain.refutes(aAtLeast100, Rel.GE));
    }

    /** What a strict bound says is kept through the reduction: under, and not at. */
    @Test
    void aStrictBoundIsStillStrictOverThePositionsLeftFree() {
        Map<String, NumberSpace> spaces = spaces(Granularity.DENSE, "a", "b", "x", "y");
        LinearForm<String> ab = sum(atom("a"), atom("b"));
        NumericDomain<String> domain = top()
                .assume(difference(atom("x"), ab), Rel.EQ, spaces)
                .assume(difference(atom("y"), ab), Rel.EQ, spaces)
                .assume(difference(atom("y"), constant(5)), Rel.LT, spaces);

        assertTrue(domain.entails(difference(atom("x"), constant(5)), Rel.LT));
        assertFalse(domain.entails(difference(atom("x"), constant(4)), Rel.LE),
                "over decimals a sum under five is not at most four");
    }

    /**
     * {@code x = 2y} with {@code y} between nought and one leaves {@code x} at nought or two, and
     * not at one: the range {@code [0, 2]} is not the whole of what the rules leave it. Asked a goal
     * the reduction answers, the domain still says so.
     */
    @Test
    void aRangeWithAHoleInItIsNotCertifiedWhetherOrNotAGoalWasAsked() {
        Map<String, NumberSpace> spaces = spaces(Granularity.DISCRETE, "x", "y");
        NumericDomain<String> domain = top()
                .assume(difference(atom("x"), atom("y").times(ExactRatio.of(2)).orNull()),
                        Rel.EQ, spaces)
                .assume(atom("y"), Rel.GE, spaces)
                .assume(difference(atom("y"), constant(1)), Rel.LE, spaces);

        assertEquals(new ProjectionCertification.NotEveryRuleIsProven(),
                domain.projectionCertification());
        domain.entails(difference(atom("x"), constant(2)), Rel.LE);
        assertEquals(new ProjectionCertification.NotEveryRuleIsProven(),
                domain.projectionCertification());
    }

    /**
     * Whole numbers and decimals tied by an equality are spaced differently, and a box over them is
     * not certified as the whole of what the rules leave.
     */
    @Test
    void aWholeNumberTiedToADecimalIsNotCertified() {
        Map<String, NumberSpace> spaces = new LinkedHashMap<>();
        spaces.put("x", NumberSpace.spacedOnly(Granularity.DISCRETE));
        spaces.put("d", NumberSpace.spacedOnly(Granularity.DENSE));
        spaces.put("e", NumberSpace.spacedOnly(Granularity.DENSE));
        NumericDomain<String> domain = top()
                .assume(difference(atom("x"), sum(atom("d"), atom("e"))), Rel.EQ, spaces)
                .assume(atom("d"), Rel.GE, spaces)
                .assume(difference(atom("d"), constant(3)), Rel.LE, spaces);

        assertEquals(new ProjectionCertification.PositionsSpacedDifferently(),
                domain.projectionCertification());
        domain.entails(difference(atom("x"), constant(9)), Rel.LE);
        assertEquals(new ProjectionCertification.PositionsSpacedDifferently(),
                domain.projectionCertification());
    }

    /** A rule over a position solved for is rewritten, whichever side of it the bound holds. */
    @Test
    void aBoundOnAPositionSolvedForIsReadOverTheFreePositions() {
        Map<String, NumberSpace> spaces = spaces(Granularity.DISCRETE, "a", "b", "x", "y");
        LinearForm<String> ab = sum(atom("a"), atom("b"));
        NumericDomain<String> domain = top()
                .assume(difference(atom("x"), ab), Rel.EQ, spaces)
                .assume(difference(atom("y"), ab), Rel.EQ, spaces)
                .assume(difference(atom("x"), constant(7)), Rel.LE, spaces);

        assertTrue(domain.entails(difference(atom("y"), constant(7)), Rel.LE));
        assertFalse(domain.entails(difference(atom("y"), constant(6)), Rel.LE));
    }
}
