package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code f /= v} beside a reach of at most {@code v} puts {@code f} below {@code v}, and that is a
 * statement about {@code f}: asked how far {@code f} runs, the answer is the one the strict
 * comparison written in its place gives.
 *
 * <p>Pinned on a sum and on a difference, where the form is not a position and its bound is not any
 * position's end, and on one position, where it is. Each case has the control that writes the
 * bound without a hole, and the ones that must not move: a hole with nothing to side it, and a
 * dense range, where {@code < v} does not become {@code <= v - 1}.
 */
class AHoleOnASumBoundsTheSumNotOnlyItsPositionsTest {

    private static final String A = "a";
    private static final String B = "b";

    private static LinearForm<String> atom(String a) {
        return LinearForm.<String>atom(a);
    }

    private static LinearForm<String> num(long n) {
        return LinearForm.<String>constant(ExactRatio.of(n));
    }

    private static Map<String, NumberSpace> spaced(Granularity g) {
        Map<String, NumberSpace> out = new LinkedHashMap<>();
        out.put(A, NumberSpace.spacedOnly(g));
        out.put(B, NumberSpace.spacedOnly(g));
        return out;
    }

    private static NumericDomain<String> start() {
        return NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
    }

    private static LinearForm<String> sumMinus(long n) {
        return SmallForm.small(atom(A)).plus(atom(B)).minus(num(n)).form();
    }

    private static LinearForm<String> differenceMinus(long n) {
        return SmallForm.small(atom(A)).minus(atom(B)).minus(num(n)).form();
    }

    private static NumericDomain<String> assumed(NumericDomain<String> from, LinearForm<String> form,
                                                 Rel rel, Granularity g) {
        return from.assume(form, rel, spaced(g));
    }

    @Test
    void aHoleBesideAnUpperBoundOnASumPutsTheSumOneStepBelow() {
        NumericDomain<String> d = assumed(assumed(assumed(start(),
                atom(B).negate(), Rel.LE, Granularity.DISCRETE),
                sumMinus(50), Rel.LE, Granularity.DISCRETE),
                sumMinus(50), Rel.NE, Granularity.DISCRETE);

        assertTrue(d.entails(sumMinus(49), Rel.LE));
        assertFalse(d.entails(sumMinus(48), Rel.LE), "a + b = 49 is admitted");
    }

    @Test
    void aHoleBesideAnUpperBoundOnADifferencePutsTheDifferenceOneStepBelow() {
        NumericDomain<String> d = assumed(assumed(start(),
                differenceMinus(50), Rel.LE, Granularity.DISCRETE),
                differenceMinus(50), Rel.NE, Granularity.DISCRETE);

        assertTrue(d.entails(differenceMinus(49), Rel.LE));
        assertFalse(d.entails(differenceMinus(48), Rel.LE), "a - b = 49 is admitted");
    }

    @Test
    void aHoleBesideALowerBoundOnASumPutsTheSumOneStepAbove() {
        NumericDomain<String> d = assumed(assumed(start(),
                sumMinus(50), Rel.GE, Granularity.DISCRETE),
                sumMinus(50), Rel.NE, Granularity.DISCRETE);

        assertTrue(d.entails(sumMinus(51), Rel.GE));
        assertFalse(d.entails(sumMinus(52), Rel.GE), "a + b = 51 is admitted");
    }

    @Test
    void overADenseRangeTheSumIsBelowTheValueAndNotAStepBelowIt() {
        NumericDomain<String> d = assumed(assumed(start(),
                sumMinus(50), Rel.LE, Granularity.DENSE),
                sumMinus(50), Rel.NE, Granularity.DENSE);

        assertTrue(d.entails(sumMinus(50), Rel.LT));
        assertFalse(d.entails(sumMinus(49), Rel.LE), "a + b = 49.5 is admitted");
    }

    @Test
    void aHoleBesideNothingBoundsNothing() {
        NumericDomain<String> d = assumed(start(), sumMinus(50), Rel.NE, Granularity.DISCRETE);

        assertFalse(d.entails(sumMinus(50), Rel.LE));
        assertFalse(d.entails(sumMinus(50), Rel.GE));
    }

    @Test
    void twoHolesBesideABoundTakeTwoStepsOffTheSum() {
        NumericDomain<String> d = assumed(assumed(assumed(start(),
                sumMinus(50), Rel.LE, Granularity.DISCRETE),
                sumMinus(50), Rel.NE, Granularity.DISCRETE),
                sumMinus(49), Rel.NE, Granularity.DISCRETE);

        assertTrue(d.entails(sumMinus(48), Rel.LE));
        assertFalse(d.entails(sumMinus(47), Rel.LE), "a + b = 48 is admitted");
    }

    @Test
    void whatIsSaidFirstDoesNotDecideWhatTheSumIsLeft() {
        NumericDomain<String> boundFirst = assumed(assumed(assumed(start(),
                sumMinus(50), Rel.LE, Granularity.DISCRETE),
                sumMinus(50), Rel.NE, Granularity.DISCRETE),
                sumMinus(49), Rel.NE, Granularity.DISCRETE);
        NumericDomain<String> holesFirst = assumed(assumed(assumed(start(),
                sumMinus(49), Rel.NE, Granularity.DISCRETE),
                sumMinus(50), Rel.NE, Granularity.DISCRETE),
                sumMinus(50), Rel.LE, Granularity.DISCRETE);

        assertTrue(holesFirst.entails(sumMinus(48), Rel.LE));
        assertEquals(boundFirst.entails(sumMinus(48), Rel.LE),
                holesFirst.entails(sumMinus(48), Rel.LE));
    }

    @Test
    void aHoleBesideTheSumPinnedAtItLeavesNothing() {
        NumericDomain<String> d = assumed(assumed(start(),
                sumMinus(50), Rel.EQ, Granularity.DISCRETE),
                sumMinus(50), Rel.NE, Granularity.DISCRETE);

        assertTrue(d.entails(sumMinus(0), Rel.LT), "no point satisfies the rules, so anything follows");
    }

    /**
     * The half-spaces a state hands to the reading are statements the rules imply, and not a
     * narrower region than they leave: every point of a small box that satisfies the rules satisfies
     * each of them.
     */
    @Test
    void everyHalfSpaceAStateStatesHoldsAtEveryPointTheRulesAdmit() {
        List<AffineConstraint<String>> rules = List.of(
                half(Map.of(B, ExactRatio.of(-1)), 0),
                half(Map.of(A, ExactRatio.ONE, B, ExactRatio.ONE), 50),
                hole(Map.of(A, ExactRatio.ONE, B, ExactRatio.ONE), 50),
                hole(Map.of(A, ExactRatio.ONE, B, ExactRatio.ONE), 49));
        Function<String, Granularity> whole = _ -> Granularity.DISCRETE;
        ClosedState<String> closed = ClosedState.of(rules, whole, CanonicalOrder.asTheyAreSpelled());

        assertFalse(closed.sided().isEmpty());
        for (long a = -60; a <= 60; a++) {
            for (long b = -60; b <= 60; b++) {
                if (b < 0 || a + b > 50 || a + b == 50 || a + b == 49) {
                    continue;
                }
                for (AffineConstraint.HalfSpace<String> each : closed.sided()) {
                    ExactRatio sum = ExactRatio.ZERO;
                    for (Map.Entry<String, ExactRatio> weighed : each.form().coefs().entrySet()) {
                        long at = weighed.getKey().equals(A) ? a : b;
                        sum = sum.plus(weighed.getValue().times(ExactRatio.of(at)).orNull()).orNull();
                    }
                    int against = sum.compareTo(each.bound().at());
                    assertTrue(against < 0 || (against == 0 && each.bound().inclusive()),
                            "(" + a + ", " + b + ") satisfies the rules and not " + each);
                }
            }
        }
    }

    private static AffineConstraint<String> half(Map<String, ExactRatio> coefs, long bound) {
        return stated(AffineConstraint.of(coefs, ExactRatio.of(-bound), Rel.LE,
                _ -> Granularity.DISCRETE));
    }

    private static AffineConstraint<String> hole(Map<String, ExactRatio> coefs, long at) {
        return stated(AffineConstraint.of(coefs, ExactRatio.of(-at), Rel.NE,
                _ -> Granularity.DISCRETE));
    }

    private static AffineConstraint<String> stated(AffineConstraint.Read<String> read) {
        return ((AffineConstraint.Read.Stated<String>) read).constraint();
    }
}
