package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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

    /**
     * A hole whose sum can still fall on either side stays open beside one that has a side, and a
     * bound derived for the sum does not make it sided: 45 satisfies every rule here.
     */
    @Test
    void aHoleWithNoSideStaysOpenBesideOneThatHasOne() {
        NumericDomain<String> d = assumed(assumed(assumed(start(),
                sumMinus(50), Rel.LE, Granularity.DISCRETE),
                sumMinus(50), Rel.NE, Granularity.DISCRETE),
                sumMinus(40), Rel.NE, Granularity.DISCRETE);

        assertTrue(d.entails(sumMinus(49), Rel.LE));
        assertFalse(d.entails(sumMinus(44), Rel.LE), "a + b = 45 is admitted");
        assertFalse(d.entails(sumMinus(40), Rel.GE), "a + b = 39 is admitted");
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

    /**
     * A run of holes longer than the rounds the box is given to settle in. Which side a hole falls
     * on never changes once it is decided and there are only as many holes as were said, so the run
     * is finished however long it is.
     */
    @Test
    void aRunOfHolesLongerThanTheRoundsIsSettledToItsEnd() {
        NumericDomain<String> d = assumed(start(), sumMinus(50), Rel.LE, Granularity.DISCRETE);
        int holes = ClosedState.ROUNDS * 2;
        for (int at = 50; at > 50 - holes; at--) {
            d = assumed(d, sumMinus(at), Rel.NE, Granularity.DISCRETE);
        }

        assertTrue(d.entails(sumMinus(50 - holes), Rel.LE));
        assertFalse(d.entails(sumMinus(49 - holes), Rel.LE), "a + b = " + (50 - holes) + " is admitted");
    }

    /**
     * Holes on two differences, each beside a bound, give the same chain as the two strict
     * comparisons written in their place.
     */
    @Test
    void holesOnTwoDifferencesComposeAsTheStrictComparisonsDo() {
        LinearForm<String> ab = SmallForm.small(atom(A)).minus(atom(B)).minus(num(3)).form();
        LinearForm<String> bc = SmallForm.small(atom(B)).minus(atom("c")).minus(num(3)).form();
        LinearForm<String> ac = SmallForm.small(atom(A)).minus(atom("c")).minus(num(4)).form();
        Map<String, NumberSpace> whole = new LinkedHashMap<>();
        for (String each : List.of(A, B, "c")) {
            whole.put(each, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        NumericDomain<String> holes = start().assume(ab, Rel.LE, whole).assume(ab, Rel.NE, whole)
                .assume(bc, Rel.LE, whole).assume(bc, Rel.NE, whole);
        NumericDomain<String> strict = start().assume(ab, Rel.LT, whole).assume(bc, Rel.LT, whole);

        assertTrue(strict.entails(ac, Rel.LE));
        assertEquals(strict.entails(ac, Rel.LE), holes.entails(ac, Rel.LE));
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

    /**
     * Holes on sums and on differences, a run of them on one sum, every position bounded: whatever
     * the state hands back — the box, the half-spaces, the closed differences — holds at every point
     * the rules admit.
     */
    @Test
    void whatAStateWithHolesHandsBackHoldsAtEveryPointTheRulesAdmit() {
        List<AffineConstraint<String>> rules = holesOnSumsAndDifferences();
        ClosedState<String> closed = ClosedState.of(rules, WHOLE, CanonicalOrder.asTheyAreSpelled());
        assertFalse(closed.holdsNothing());

        for (long a = -12; a <= 16; a++) {
            for (long b = -12; b <= 16; b++) {
                for (long c = -2; c <= 7; c++) {
                    Map<String, Long> at = Map.of(A, a, B, b, "c", c);
                    if (!admits(rules, at)) {
                        continue;
                    }
                    for (String each : List.of(A, B, "c")) {
                        ExactCut low = closed.box().leastOf(each);
                        ExactCut high = closed.box().mostOf(each);
                        assertTrue(low == null || below(low, at.get(each), true),
                                each + " = " + at.get(each) + " is under " + low);
                        assertTrue(high == null || below(high, at.get(each), false),
                                each + " = " + at.get(each) + " is over " + high);
                    }
                    for (AffineConstraint.HalfSpace<String> each : closed.sided()) {
                        assertTrue(satisfies(each, at), at + " does not satisfy " + each);
                    }
                    for (DifferenceBounds.Apart<String> each : closed.differences().relations()) {
                        long gap = at.get(each.above()) - at.get(each.below());
                        assertTrue(below(each.by(), gap, false),
                                at + " is further apart than " + each);
                    }
                }
            }
        }
        assertTrue(closed.sided().contains(half(AC, 4)),
                "the run of holes took the sum from 10 down to 4: " + closed.sided());
    }

    /**
     * What a state carries from one round to the next is what settling from nothing comes to. The
     * holes an earlier round sided are not asked again, and that is only a saving where the answer
     * is the one asking would give.
     */
    @Test
    void holesCarriedFromEarlierRoundsAreTheHolesSettledFromNothing() {
        List<AffineConstraint<String>> rules = holesOnSumsAndDifferences();
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        ClosedState<String> closed = ClosedState.of(rules, WHOLE, order);
        assertEquals(ClosedState.Status.STABLE, closed.status());

        FormReach<String> fromNothing = FormReach.over(rules, closed.box(), closed.differences(), order);
        AffineReduction.Reduction.Tightened<String> found = (AffineReduction.Reduction.Tightened<String>)
                AffineReduction.over(fromNothing, WHOLE, order);

        assertEquals(found.sided(), closed.sided());
    }

    /**
     * A hole the closed differences state is something the certificate may rest on, and one they do
     * not state is not. The differences hold the half-space a hole on a difference came to, and hold
     * nothing about a sum.
     */
    @Test
    void aHoleIsCertifiedWhereTheClosedDifferencesStateItAndNotOnASum() {
        Map<String, NumberSpace> whole = spaced(Granularity.DISCRETE);
        NumericDomain<String> onADifference = start().assume(differenceMinus(3), Rel.LE, whole)
                .assume(differenceMinus(3), Rel.NE, whole);
        NumericDomain<String> onASum = start().assume(sumMinus(3), Rel.LE, whole)
                .assume(sumMinus(3), Rel.NE, whole);

        assertInstanceOf(ProjectionCertification.Certified.class,
                onADifference.projectionCertification());
        assertInstanceOf(ProjectionCertification.NotEveryRuleIsProven.class,
                onASum.projectionCertification());
    }

    private static final Function<String, Granularity> WHOLE = _ -> Granularity.DISCRETE;

    private static final Map<String, ExactRatio> AB = Map.of(A, ExactRatio.ONE, B, ExactRatio.of(-1));
    private static final Map<String, ExactRatio> BC = Map.of(B, ExactRatio.ONE, "c", ExactRatio.of(-1));
    private static final Map<String, ExactRatio> AC = Map.of(A, ExactRatio.ONE, "c", ExactRatio.ONE);

    /** Holes on two differences, each beside a bound; and on a sum, a run of them from its bound
     *  down, with a position the sum names bounded both ways. */
    private static List<AffineConstraint<String>> holesOnSumsAndDifferences() {
        List<AffineConstraint<String>> rules = new ArrayList<>(List.of(
                half(AB, 3), hole(AB, 3), half(BC, 3), hole(BC, 3),
                half(Map.of("c", ExactRatio.ONE), 5), half(Map.of("c", ExactRatio.of(-1)), 0),
                half(AC, 10)));
        for (long at = 10; at >= 5; at--) {
            rules.add(hole(AC, at));
        }
        return rules;
    }

    /** Whether {@code value} is on the inner side of {@code cut}: at or above it for a lower end,
     *  at or below it for an upper. */
    private static boolean below(ExactCut cut, long value, boolean lowerEnd) {
        int order = ExactRatio.of(value).compareTo(cut.at());
        int towards = lowerEnd ? order : -order;
        return towards > 0 || (towards == 0 && cut.inclusive());
    }

    private static boolean satisfies(AffineConstraint.HalfSpace<String> half, Map<String, Long> at) {
        ExactRatio weighed = ExactRatio.ZERO;
        for (Map.Entry<String, ExactRatio> each : half.form().coefs().entrySet()) {
            weighed = weighed.plus(each.getValue().times(ExactRatio.of(at.get(each.getKey())))
                    .orNull()).orNull();
        }
        int against = weighed.compareTo(half.bound().at());
        return against < 0 || (against == 0 && half.bound().inclusive());
    }

    private static boolean admits(List<AffineConstraint<String>> rules, Map<String, Long> at) {
        for (AffineConstraint<String> each : rules) {
            ExactRatio weighed = ExactRatio.ZERO;
            for (Map.Entry<String, ExactRatio> term : each.form().coefs().entrySet()) {
                weighed = weighed.plus(term.getValue().times(ExactRatio.of(at.get(term.getKey())))
                        .orNull()).orNull();
            }
            boolean holds = switch (each) {
                case AffineConstraint.HalfSpace<String> half -> satisfies(half, at);
                case AffineConstraint.Equality<String> equal -> weighed.compareTo(equal.at()) == 0;
                case AffineConstraint.Disequality<String> hole -> weighed.compareTo(hole.at()) != 0;
            };
            if (!holds) {
                return false;
            }
        }
        return true;
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
