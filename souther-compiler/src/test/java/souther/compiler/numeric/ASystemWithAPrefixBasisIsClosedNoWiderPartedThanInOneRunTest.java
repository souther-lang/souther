package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.RulesAsWritten.Written;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.positionsOf;
import static souther.compiler.numeric.RulesAsWritten.rule;
import static souther.compiler.numeric.RulesAsWritten.statedOnly;

/**
 * Rules that name no position in common are closed apart, and where a part is a chain of prefix
 * sums it is closed in a basis, exactly. Closing all the rules in one run is not parted, so no basis
 * is chosen for it and it is the derivation by rounds alone.
 *
 * <p>Three things are said of the two, and they are not one thing. What the rules denote is the
 * product of what each part denotes, which is not what is held here. What the canonical closure is
 * — each part closed and the closures put together — is the same however it is reached: parted
 * through {@link ClosedState#of}, kept a part at a time, or each part closed on its own and
 * multiplied, in everything it answers. And how it stands beside the closure in one run, the other
 * derivation of the same rules: the box is never wider, it holds nothing wherever the closure in
 * one run does, and a form over several positions is proven wherever the closure in one run proves
 * it, and some it does not.
 *
 * <p>That the box is within is a claim about the basis and the rounds and not about soundness
 * alone, since both are sound and neither need be within the other. Over every chain drawn the two
 * boxes are in fact one: the rounds read each sum as a premise and find what the basis finds. What
 * the basis has and the rounds have not is the answer for a form that is a run of positions, and
 * that is where the product is strictly within, and where a basis wrongly not chosen would show.
 */
class ASystemWithAPrefixBasisIsClosedNoWiderPartedThanInOneRunTest {

    private static final CanonicalOrder<String> SPELLED = CanonicalOrder.asTheyAreSpelled();

    private static Granularity whole(String ignored) {
        return Granularity.DISCRETE;
    }

    private static List<AffineConstraint<String>> stated(List<Written> written) {
        return statedOnly(written,
                ASystemWithAPrefixBasisIsClosedNoWiderPartedThanInOneRunTest::whole);
    }

    private static PrefixBasis<String> basisOver(List<AffineConstraint<String>> rules) {
        return PrefixBasis.over(rules,
                ASystemWithAPrefixBasisIsClosedNoWiderPartedThanInOneRunTest::whole, SPELLED);
    }

    private static ClosedState<String> inOneRun(List<AffineConstraint<String>> rules) {
        return ClosedState.closedTogether(rules,
                ASystemWithAPrefixBasisIsClosedNoWiderPartedThanInOneRunTest::whole, SPELLED);
    }

    /** What the canonical closure is, reached the three ways there are, and what each answers. */
    private static ClosedState<String> canonical(List<AffineConstraint<String>> rules) {
        ClosedState<String> parted = ClosedState.of(rules,
                ASystemWithAPrefixBasisIsClosedNoWiderPartedThanInOneRunTest::whole, SPELLED);
        ClosedState<String> kept = ClosedStates.kept().of(rules,
                ASystemWithAPrefixBasisIsClosedNoWiderPartedThanInOneRunTest::whole, SPELLED);
        List<ClosedState<String>> each = new ArrayList<>();
        for (List<AffineConstraint<String>> part : ClosureQuestion.independentRules(rules)) {
            each.add(inOneRun(part));
        }
        ClosedState<String> product = ClosedState.product(each);

        assertEquals(RulesNamingNoPositionInCommonCloseApartTest.outcome(parted),
                RulesNamingNoPositionInCommonCloseApartTest.outcome(kept), "kept: " + rules);
        assertEquals(RulesNamingNoPositionInCommonCloseApartTest.outcome(parted),
                RulesNamingNoPositionInCommonCloseApartTest.outcome(product), "product: " + rules);
        return parted;
    }

    /** Whether {@code tight} leaves no more than {@code loose} on a side, where null is no end. */
    private static boolean noWiderAbove(ExactCut tight, ExactCut loose) {
        return loose == null || (tight != null && ExactCut.tighterUpper(tight, loose).equals(tight));
    }

    private static boolean noWiderBelow(ExactCut tight, ExactCut loose) {
        return loose == null || (tight != null && ExactCut.tighterLower(tight, loose).equals(tight));
    }

    /** The canonical closure of {@code rules} is no wider than their closure in one run. */
    private static void partedIsWithinInOneRun(List<AffineConstraint<String>> rules,
                                               List<String> positions, String where) {
        ClosedState<String> parted = canonical(rules);
        ClosedState<String> inOneRun = inOneRun(rules);
        if (inOneRun.holdsNothing()) {
            assertTrue(parted.holdsNothing(), "the rounds showed nothing is left and the basis did"
                    + " not: " + where);
            return;
        }
        if (parted.holdsNothing()) {
            return;
        }
        for (String position : positions) {
            assertTrue(noWiderAbove(parted.box().mostOf(position), inOneRun.box().mostOf(position)),
                    "wider above " + position + ": " + where);
            assertTrue(noWiderBelow(parted.box().leastOf(position), inOneRun.box().leastOf(position)),
                    "wider below " + position + ": " + where);
        }
    }

    @Test
    void aChainBesideRulesOfItsOwnIsClosedNoWiderPartedThanInOneRun() {
        Random random = new Random(3184);
        int compared = 0;
        for (int round = 0; round < 300; round++) {
            List<Written> written = new ArrayList<>(
                    PrefixChains.chain(random, 2 + random.nextInt(3)));
            List<AffineConstraint<String>> chain = stated(written);
            written.add(rule("x - y <= 2"));
            written.add(rule("x >= 0"));
            written.add(rule("zz <= " + random.nextInt(5)));
            List<AffineConstraint<String>> rules = stated(written);
            // Compared where there is a basis to choose and the rules in one run do not choose it.
            assertNotNull(basisOver(chain));
            assertNull(basisOver(rules));
            partedIsWithinInOneRun(rules, new ArrayList<>(positionsOf(written)), written.toString());
            compared++;
        }
        assertEquals(300, compared);
    }

    /**
     * Where the product is strictly within: what a domain proves of a form over two positions. The
     * rules say {@code a + b} is at most -3 and {@code a + b + c + d} at least 2, so {@code c + d}
     * is at least 5, which is the difference of two coordinates of the basis. The rules in one run
     * have no basis, and read a form of two positions from the ends of each and the sums as premises
     * to a bound of 2.
     */
    @Test
    void aFormOverTwoPositionsIsProvenParted() {
        List<Written> written = new ArrayList<>(List.of(rule("a >= -2"), rule("a <= 5"),
                rule("b >= -4"), rule("b <= 4"), rule("c >= -2"), rule("c <= 5"), rule("d >= -3"),
                rule("d <= 5"), rule("a + b < -2"), rule("a + b + c > -3"),
                rule("a + b + c + d > 1")));
        written.add(rule("x <= 3"));
        List<AffineConstraint<String>> rules = stated(written);

        assertNull(basisOver(rules));
        Map<String, ExactRatio> cd = new LinkedHashMap<>();
        cd.put("c", ExactRatio.ONE.negated());
        cd.put("d", ExactRatio.ONE.negated());
        assertEquals(new PrefixBasis.Highest.Within(ExactCut.inclusive(ExactRatio.of(-5))),
                canonical(rules).highestInBasis(cd, ExactRatio.ZERO));
        assertSame(PrefixBasis.Highest.NOT_ANSWERED, inOneRun(rules).highestInBasis(cd,
                ExactRatio.ZERO));

        Map<String, NumberSpace> spaces = new LinkedHashMap<>();
        for (String atom : List.of("a", "b", "c", "d", "x")) {
            spaces.put(atom, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        NumericDomain<String> parted = NumericDomain.top(SPELLED, ClosedStates.kept());
        NumericDomain<String> unparted = NumericDomain.top(SPELLED, ClosedStates.IN_ONE_RUN);
        for (Written each : written) {
            LinearForm<String> form = new LinearForm<>(each.constant(), each.coefs());
            parted = parted.assume(form, each.rel(), spaces);
            unparted = unparted.assume(form, each.rel(), spaces);
        }
        Map<String, ExactRatio> sum = new LinkedHashMap<>();
        sum.put("c", ExactRatio.ONE);
        sum.put("d", ExactRatio.ONE);

        assertTrue(parted.entails(new LinearForm<>(ExactRatio.of(-5), sum), Rel.GE));
        assertFalse(unparted.entails(new LinearForm<>(ExactRatio.of(-5), sum), Rel.GE));
        // What the rounds prove the basis proves: the one is within the other, not the other way.
        assertTrue(parted.entails(new LinearForm<>(ExactRatio.of(-2), sum), Rel.GE));
        assertTrue(unparted.entails(new LinearForm<>(ExactRatio.of(-2), sum), Rel.GE));
        assertInstanceOf(NumericDomain.FormProjection.Within.class,
                parted.projectionOf(new LinearForm<>(ExactRatio.ZERO, sum)));
    }
}
