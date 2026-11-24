package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.RulesAsWritten.Written;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;
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
 * <p>Which of these is held of rules is decided before the closures are worked out, by whether a
 * part of them has a basis ({@link #selectsABasis}), and never by whether the closures turned out
 * alike: a difference between the two that nothing accounts for is the claim failing, where a
 * difference that is skipped hides whatever else made it. {@link #theSpecialisedContract} is what
 * is held of rules with a basis part, and the equality of every observable, of those with none
 * ({@link RulesNamingNoPositionInCommonCloseApartTest}).
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

    /** Whether a part of {@code rules} has a basis: the rules are then closed by it, parted. */
    static boolean selectsABasis(List<AffineConstraint<String>> rules,
                                 Function<String, Granularity> spacing,
                                 CanonicalOrder<String> order) {
        for (List<AffineConstraint<String>> part : ClosureQuestion.independentRules(rules)) {
            if (PrefixBasis.over(part, spacing, order) != null) {
                return true;
            }
        }
        return false;
    }

    private static Set<String> positionsIn(List<AffineConstraint<String>> rules) {
        Set<String> out = new LinkedHashSet<>();
        rules.forEach(each -> out.addAll(each.form().coefs().keySet()));
        return out;
    }

    /** Whether {@code tight} leaves no more than {@code loose} on a side, where null is no end. */
    private static boolean noWiderAbove(ExactCut tight, ExactCut loose) {
        return loose == null || (tight != null && ExactCut.tighterUpper(tight, loose).equals(tight));
    }

    private static boolean noWiderBelow(ExactCut tight, ExactCut loose) {
        return loose == null || (tight != null && ExactCut.tighterLower(tight, loose).equals(tight));
    }

    /**
     * What is held of rules some part of which has a basis: the canonical closure is one however it
     * is reached, a part closed in a basis is settled and composed, and the canonical closure is no
     * wider than the closure in one run.
     */
    static void theSpecialisedContract(List<AffineConstraint<String>> rules,
                                       Function<String, Granularity> spacing,
                                       CanonicalOrder<String> order, String where) {
        assertTrue(selectsABasis(rules, spacing, order),
                "held of rules with a basis part, and these have none: " + where);
        ClosedState<String> parted = ClosedState.of(rules, spacing, order);
        ClosedState<String> kept = ClosedStates.kept().of(rules, spacing, order);
        List<List<AffineConstraint<String>>> parts = ClosureQuestion.independentRules(rules);
        List<ClosedState<String>> each = new ArrayList<>();
        for (List<AffineConstraint<String>> part : parts) {
            each.add(ClosedState.closedTogether(part, spacing, order));
        }

        assertEquals(RulesNamingNoPositionInCommonCloseApartTest.outcome(parted),
                RulesNamingNoPositionInCommonCloseApartTest.outcome(kept), "kept: " + where);
        assertEquals(RulesNamingNoPositionInCommonCloseApartTest.outcome(parted),
                RulesNamingNoPositionInCommonCloseApartTest.outcome(ClosedState.product(each)),
                "product: " + where);
        // What a part closed in a basis says of itself: the rounds are not run, so it stopped, and
        // every bound it holds was composed.
        for (int at = 0; at < parts.size(); at++) {
            if (PrefixBasis.over(parts.get(at), spacing, order) != null
                    && !each.get(at).holdsNothing()) {
                assertEquals(ClosedState.Status.STABLE, each.get(at).status(), where);
                assertTrue(each.get(at).isSettledAndComposed(), where);
            }
        }

        ClosedState<String> inOneRun = ClosedState.closedTogether(rules, spacing, order);
        if (inOneRun.holdsNothing()) {
            assertTrue(parted.holdsNothing(), "the rounds showed nothing is left and the basis did"
                    + " not: " + where);
            return;
        }
        if (parted.holdsNothing()) {
            return;
        }
        for (String position : positionsIn(rules)) {
            assertTrue(noWiderAbove(parted.box().mostOf(position), inOneRun.box().mostOf(position)),
                    "wider above " + position + ": " + where);
            assertTrue(noWiderBelow(parted.box().leastOf(position), inOneRun.box().leastOf(position)),
                    "wider below " + position + ": " + where);
        }
    }

    @Test
    void aChainBesideRulesOfItsOwnIsClosedNoWiderPartedThanInOneRun() {
        Random random = new Random(3184);
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
            theSpecialisedContract(rules,
                    ASystemWithAPrefixBasisIsClosedNoWiderPartedThanInOneRunTest::whole, SPELLED,
                    written.toString());
        }
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
        ClosedState<String> parted = ClosedState.of(rules,
                ASystemWithAPrefixBasisIsClosedNoWiderPartedThanInOneRunTest::whole, SPELLED);
        ClosedState<String> inOneRun = ClosedState.closedTogether(rules,
                ASystemWithAPrefixBasisIsClosedNoWiderPartedThanInOneRunTest::whole, SPELLED);
        assertEquals(new PrefixBasis.Highest.Within(ExactCut.inclusive(ExactRatio.of(-5))),
                parted.highestInBasis(cd, ExactRatio.ZERO));
        assertSame(PrefixBasis.Highest.NOT_ANSWERED, inOneRun.highestInBasis(cd, ExactRatio.ZERO));

        Map<String, NumberSpace> spaces = new LinkedHashMap<>();
        for (String atom : List.of("a", "b", "c", "d", "x")) {
            spaces.put(atom, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        NumericDomain<String> keptDomain = NumericDomain.top(SPELLED, ClosedStates.kept());
        NumericDomain<String> unparted = NumericDomain.top(SPELLED, ClosedStates.IN_ONE_RUN);
        for (Written each : written) {
            LinearForm<String> form = new LinearForm<>(each.constant(), each.coefs());
            keptDomain = keptDomain.assume(form, each.rel(), spaces);
            unparted = unparted.assume(form, each.rel(), spaces);
        }
        Map<String, ExactRatio> sum = new LinkedHashMap<>();
        sum.put("c", ExactRatio.ONE);
        sum.put("d", ExactRatio.ONE);

        assertTrue(keptDomain.entails(new LinearForm<>(ExactRatio.of(-5), sum), Rel.GE));
        assertFalse(unparted.entails(new LinearForm<>(ExactRatio.of(-5), sum), Rel.GE));
        // What the rounds prove the basis proves: the one is within the other, not the other way.
        assertTrue(keptDomain.entails(new LinearForm<>(ExactRatio.of(-2), sum), Rel.GE));
        assertTrue(unparted.entails(new LinearForm<>(ExactRatio.of(-2), sum), Rel.GE));
        assertInstanceOf(NumericDomain.FormProjection.Within.class,
                keptDomain.projectionOf(new LinearForm<>(ExactRatio.ZERO, sum)));
    }
}
