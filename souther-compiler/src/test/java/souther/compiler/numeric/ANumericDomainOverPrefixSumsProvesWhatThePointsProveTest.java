package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.RulesAsWritten.Written;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.PrefixChains.ATOMS;
import static souther.compiler.numeric.PrefixChains.REACH;
import static souther.compiler.numeric.RulesAsWritten.pointsSatisfying;
import static souther.compiler.numeric.RulesAsWritten.rule;
import static souther.compiler.numeric.RulesAsWritten.someRuleHoldsNever;

/**
 * What a domain over rules that are sums of one growing prefix proves of a form is what the
 * whole-numbered points satisfying the rules prove of it — asked through what a caller sees:
 * {@code entails}, {@code refutes}, {@code boundsOf} and
 * {@code provenByTheBoxAndItsDifferences}.
 *
 * <p>The rules are closed in a basis there, and a form that comes to one coordinate or the
 * difference of two in it is answered from the basis and every other form from the rules as they
 * are stated. Held here, against every point over a small range, for each form and each bound put
 * to it:
 *
 * <ul>
 *   <li>nothing is proven that a point does not bear out, and nothing is refuted that a point
 *       satisfies;</li>
 *   <li>a form the basis answers is proven exactly: at the most it comes to and not below it;</li>
 *   <li>what the rules read as they are stated prove is proven here too, over the same rules with
 *       one more beside them that keeps the basis from being chosen, for every form, those it does
 *       not answer included;</li>
 *   <li>the question of what the ranges and the differences prove stays a question of those and
 *       not of the rules: a sum the ranges cannot show is not shown by them.</li>
 * </ul>
 */
class ANumericDomainOverPrefixSumsProvesWhatThePointsProveTest {

    private static final CanonicalOrder<String> SPELLED = CanonicalOrder.asTheyAreSpelled();

    /** A bound no sum with a small number has a representation for. */
    private static final ExactRatio HUGE =
            ExactRatio.of(new BigDecimal(BigInteger.ONE, -Integer.MAX_VALUE));

    private static Map<String, NumberSpace> spaces() {
        Map<String, NumberSpace> out = new LinkedHashMap<>();
        for (String atom : List.of("a", "b", "c", "d", "z")) {
            out.put(atom, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        return out;
    }

    private static NumericDomain<String> domainOf(List<Written> rules) {
        return domainOf(rules, ClosedStates.NONE);
    }

    private static NumericDomain<String> domainOf(List<Written> rules, ClosedStates table) {
        NumericDomain<String> domain = NumericDomain.top(SPELLED, table);
        Map<String, NumberSpace> spaces = spaces();
        for (Written each : rules) {
            domain = domain.assume(new LinearForm<>(each.constant(), each.coefs()), each.rel(),
                    spaces);
        }
        return domain;
    }

    /** {@code coefs} less {@code at}: what is asked to decide whether the form is below {@code at}. */
    private static LinearForm<String> below(Map<String, ExactRatio> coefs, long at) {
        return new LinearForm<>(ExactRatio.of(-at), coefs);
    }

    /** A form asked about, and whether the basis is the one to answer it. */
    private record Query(Map<String, ExactRatio> coefs, boolean inTheBasis, boolean free) {

        @Override
        public String toString() {
            return coefs.toString();
        }
    }

    private static Map<String, ExactRatio> weights(List<String> atoms, long weight) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        for (String atom : atoms) {
            out.put(atom, ExactRatio.of(weight));
        }
        return out;
    }

    /**
     * Every run of positions summed, either way up, which is one coordinate or the difference of two
     * in the basis; and forms that are neither: a weighted sum, a difference of two positions, and
     * a sum with a position no rule names.
     */
    private static List<Query> queries(List<String> atoms) {
        List<Query> out = new ArrayList<>();
        for (int from = 0; from < atoms.size(); from++) {
            for (int to = from; to < atoms.size(); to++) {
                out.add(new Query(weights(atoms.subList(from, to + 1), 1), true, false));
                out.add(new Query(weights(atoms.subList(from, to + 1), -1), true, false));
            }
        }
        Map<String, ExactRatio> weighted = new LinkedHashMap<>();
        weighted.put("a", ExactRatio.of(2));
        weighted.put("b", ExactRatio.ONE);
        out.add(new Query(weighted, false, false));
        Map<String, ExactRatio> difference = new LinkedHashMap<>();
        difference.put("a", ExactRatio.ONE);
        difference.put("b", ExactRatio.ONE.negated());
        out.add(new Query(difference, false, false));
        Map<String, ExactRatio> beside = new LinkedHashMap<>();
        beside.put("a", ExactRatio.ONE);
        beside.put("z", ExactRatio.ONE);
        out.add(new Query(beside, false, true));
        return out;
    }

    private static long valueAt(Map<String, ExactRatio> coefs, Map<String, Integer> point) {
        long sum = 0;
        for (Map.Entry<String, ExactRatio> each : coefs.entrySet()) {
            sum += Long.parseLong(each.getValue().toString()) * point.get(each.getKey());
        }
        return sum;
    }

    @Test
    void whatTheDomainProvesIsWhatThePointsProve() {
        Random random = new Random(3184);
        int exact = 0;
        int answeredByTheRulesAsStated = 0;
        int kept = 0;
        int boxWeaker = 0;
        for (int round = 0; round < 250; round++) {
            List<String> atoms = ATOMS.subList(0, 2 + random.nextInt(3));
            List<Written> written = PrefixChains.chain(random, atoms.size());
            if (someRuleHoldsNever(written, ANumericDomainOverPrefixSumsProvesWhatThePointsProveTest::whole)) {
                continue;
            }
            List<Map<String, Integer>> points = pointsSatisfying(written, atoms, -REACH, REACH);
            if (points.isEmpty()) {
                continue;
            }
            kept++;
            List<Written> apart = new ArrayList<>(written);
            apart.add(rule("a - z <= 0"));
            NumericDomain<String> basis = domainOf(written);
            NumericDomain<String> stated = domainOf(apart);
            NumericDomain<String> keptApart = domainOf(written, ClosedStates.kept());
            assertFalse(basis.isBottom(), "the points are there: " + written);
            for (Query query : queries(atoms)) {
                long most = Long.MIN_VALUE;
                long least = Long.MAX_VALUE;
                if (!query.free()) {
                    for (Map<String, Integer> point : points) {
                        most = Math.max(most, valueAt(query.coefs(), point));
                        least = Math.min(least, valueAt(query.coefs(), point));
                    }
                }
                for (long at = query.free() ? -3 : least - 1; at <= (query.free() ? 3 : most + 1);
                        at++) {
                    LinearForm<String> form = below(query.coefs(), at);
                    String where = query + " at " + at + " over " + written;
                    boolean below = basis.entails(form, Rel.LE);
                    boolean above = basis.entails(form, Rel.GE);
                    boolean refutesBelow = basis.refutes(form, Rel.LE);
                    boolean refutesAbove = basis.refutes(form, Rel.GE);
                    boolean byTheBox = basis.provenByTheBoxAndItsDifferences(form, Rel.LE);
                    // The same rules say the same whether the closures are kept or not.
                    assertEquals(below, keptApart.entails(form, Rel.LE), "kept: " + where);
                    assertEquals(above, keptApart.entails(form, Rel.GE), "kept: " + where);
                    assertEquals(refutesBelow, keptApart.refutes(form, Rel.LE), "kept: " + where);
                    assertEquals(refutesAbove, keptApart.refutes(form, Rel.GE), "kept: " + where);
                    assertEquals(byTheBox,
                            keptApart.provenByTheBoxAndItsDifferences(form, Rel.LE), "kept: " + where);
                    if (query.free()) {
                        assertFalse(below || above || refutesBelow || refutesAbove, where);
                        continue;
                    }
                    // Nothing is proven that a point does not bear out.
                    assertTrue(!below || most <= at, "proves what a point denies: " + where);
                    assertTrue(!above || least >= at, "proves what a point denies: " + where);
                    assertTrue(!refutesBelow || least > at, "refutes what a point satisfies: " + where);
                    assertTrue(!refutesAbove || most < at, "refutes what a point satisfies: " + where);
                    assertTrue(!byTheBox || most <= at, "the box proves what a point denies: " + where);
                    // A form the basis answers is proven exactly.
                    if (query.inTheBasis()) {
                        assertEquals(most <= at, below, "exactly at the most: " + where);
                        assertEquals(least >= at, above, "exactly at the least: " + where);
                        exact++;
                        if (below && !byTheBox) {
                            boxWeaker++;
                        }
                    }
                    // Whatever the rules as they are stated prove, the basis proves.
                    assertTrue(!stated.entails(form, Rel.LE) || below, "weaker: " + where);
                    assertTrue(!stated.entails(form, Rel.GE) || above, "weaker: " + where);
                    assertTrue(!stated.refutes(form, Rel.LE) || refutesBelow, "weaker: " + where);
                    assertTrue(!stated.refutes(form, Rel.GE) || refutesAbove, "weaker: " + where);
                    assertTrue(!stated.provenByTheBoxAndItsDifferences(form, Rel.LE) || byTheBox,
                            "weaker: " + where);
                    if (!query.inTheBasis()) {
                        answeredByTheRulesAsStated++;
                    }
                }
                if (query.inTheBasis()) {
                    Bounds bounds = basis.boundsOf(new LinearForm<>(ExactRatio.ZERO, query.coefs()));
                    assertEquals(Endpoint.inclusive(new Count(BigDecimal.valueOf(most))),
                            bounds.max(), query + " over " + written);
                    assertEquals(Endpoint.inclusive(new Count(BigDecimal.valueOf(least))),
                            bounds.min(), query + " over " + written);
                }
            }
        }
        assertTrue(kept > 100, "kept " + kept);
        assertTrue(exact > 3000, "exact " + exact);
        assertTrue(answeredByTheRulesAsStated > 1000, "stated " + answeredByTheRulesAsStated);
        // The control: the box and the differences are asked on their own, so what only the basis
        // knows — a sum the two ranges cannot show — is not shown by them.
        assertTrue(boxWeaker > 0, "the box alone proved every sum the rules did");
    }

    private static Granularity whole(String ignored) {
        return Granularity.DISCRETE;
    }

    /**
     * The two ranges and the sum beside them: the sum is a rule and so proven, and not by the box
     * and the differences, which hold {@code a} and {@code b} up to five each.
     */
    @Test
    void whatTheBoxAndTheDifferencesProveStaysWhatTheyProve() {
        NumericDomain<String> domain = domainOf(List.of(rule("a >= 0"), rule("a <= 5"),
                rule("b >= 0"), rule("b <= 5"), rule("a + b <= 7")));
        Map<String, ExactRatio> sum = weights(List.of("a", "b"), 1);
        Map<String, ExactRatio> a = weights(List.of("a"), 1);

        assertTrue(domain.entails(below(sum, 7), Rel.LE));
        assertFalse(domain.provenByTheBoxAndItsDifferences(below(sum, 7), Rel.LE));
        assertTrue(domain.provenByTheBoxAndItsDifferences(below(a, 5), Rel.LE));
    }

    /**
     * A form the basis does not answer is asked of the rules as they are stated, and so is one
     * whose sum the exact arithmetic cannot hold: it is neither answered as bounded by nothing nor
     * answered from the basis.
     */
    @Test
    void aFormTheBasisDoesNotAnswerIsAskedOfTheRulesAsTheyAreStated() {
        List<Written> rules = List.of(rule("a >= 0"), rule("a <= 5"), rule("b >= 0"),
                rule("b <= 5"), rule("a + b <= 7"));
        List<Written> apart = new ArrayList<>(rules);
        apart.add(rule("a - z <= 0"));
        NumericDomain<String> basis = domainOf(rules);
        NumericDomain<String> stated = domainOf(apart);
        Map<String, ExactRatio> difference = new LinkedHashMap<>();
        difference.put("a", ExactRatio.ONE);
        difference.put("b", ExactRatio.ONE.negated());
        Map<String, ExactRatio> weighted = new LinkedHashMap<>();
        weighted.put("a", ExactRatio.of(2));
        weighted.put("b", ExactRatio.ONE);

        assertTrue(basis.entails(below(difference, 5), Rel.LE));
        assertFalse(basis.entails(below(difference, 4), Rel.LE));
        assertTrue(basis.entails(below(weighted, 12), Rel.LE));
        assertFalse(basis.entails(below(weighted, 11), Rel.LE));

        LinearForm<String> beyond = new LinearForm<>(HUGE.negated(), weights(List.of("a"), 1));
        assertEquals(stated.entails(beyond, Rel.LE), basis.entails(beyond, Rel.LE));
        assertEquals(stated.refutes(beyond, Rel.LE), basis.refutes(beyond, Rel.LE));
        assertNotNull(basis.boundsOf(new LinearForm<>(HUGE, weights(List.of("a"), 1))));
    }
}
