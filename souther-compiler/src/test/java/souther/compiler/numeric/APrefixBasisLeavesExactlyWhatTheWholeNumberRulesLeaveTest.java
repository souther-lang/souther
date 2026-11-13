package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.PrefixBasis.Highest;
import souther.compiler.numeric.RulesAsWritten.Written;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.PrefixChains.ATOMS;
import static souther.compiler.numeric.PrefixChains.REACH;
import static souther.compiler.numeric.RulesAsWritten.pointsSatisfying;
import static souther.compiler.numeric.RulesAsWritten.rule;
import static souther.compiler.numeric.RulesAsWritten.someRuleHoldsNever;
import static souther.compiler.numeric.RulesAsWritten.statedOnly;

/**
 * Rules that are sums of one growing prefix, closed in the basis where each sum is one position,
 * leave each position exactly what the whole-numbered points satisfying them leave it — and answer
 * a form that comes to one coordinate or a difference the same way.
 *
 * <p>The points are every whole-numbered assignment over a small range that satisfies every rule as
 * written, so what is compared to is arithmetic on the rules and nothing this package derives. Each
 * position is boxed within the range, so no solution is left out of the points. Held beside that:
 * the state is never wider than the closure of the same rules read as they are stated (a rule that
 * is not a half-space keeps the basis from being chosen), which position of the first prefix is
 * taken first does not change what any position is left, and a basis is chosen only where it
 * answers completely: where the exact arithmetic could not sum a hop there is none, and a form it
 * cannot sum the answer of is not answered rather than answered as bounded by nothing.
 */
class APrefixBasisLeavesExactlyWhatTheWholeNumberRulesLeaveTest {

    private static final CanonicalOrder<String> SPELLED = CanonicalOrder.asTheyAreSpelled();

    /** A bound no sum with a small number has a representation for. */
    private static final ExactRatio HUGE =
            ExactRatio.of(new BigDecimal(BigInteger.ONE, -Integer.MAX_VALUE));

    private static Granularity whole(String ignored) {
        return Granularity.DISCRETE;
    }

    private static List<AffineConstraint<String>> stated(List<Written> written) {
        return statedOnly(written, APrefixBasisLeavesExactlyWhatTheWholeNumberRulesLeaveTest::whole);
    }

    private static boolean holdsNever(List<Written> written) {
        return someRuleHoldsNever(written,
                APrefixBasisLeavesExactlyWhatTheWholeNumberRulesLeaveTest::whole);
    }

    private static PrefixBasis<String> basisOver(List<AffineConstraint<String>> rules) {
        return PrefixBasis.over(rules,
                APrefixBasisLeavesExactlyWhatTheWholeNumberRulesLeaveTest::whole, SPELLED);
    }

    private static ClosedState<String> closed(List<AffineConstraint<String>> rules,
                                              CanonicalOrder<String> order) {
        return ClosedState.closedTogether(rules,
                APrefixBasisLeavesExactlyWhatTheWholeNumberRulesLeaveTest::whole, order);
    }

    @Test
    void theBoxIsWhatThePointsLeaveEachPosition() {
        Random random = new Random(3167);
        int chosen = 0;
        int cases = 0;
        int empty = 0;
        for (int round = 0; round < 600; round++) {
            List<String> atoms = ATOMS.subList(0, 2 + random.nextInt(3));
            List<Written> written = PrefixChains.chain(random, atoms.size());
            if (holdsNever(written)) {
                continue;
            }
            List<AffineConstraint<String>> rules = stated(written);
            cases++;
            if (basisOver(rules) == null) {
                continue;
            }
            chosen++;
            ClosedState<String> state = closed(rules, SPELLED);
            List<Map<String, Integer>> points = pointsSatisfying(written, atoms, -REACH, REACH);
            assertEquals(points.isEmpty(), state.holdsNothing(), written.toString());
            if (points.isEmpty()) {
                empty++;
                continue;
            }
            for (String atom : atoms) {
                int least = points.stream().mapToInt(point -> point.get(atom)).min().orElseThrow();
                int most = points.stream().mapToInt(point -> point.get(atom)).max().orElseThrow();
                assertEquals(ExactCut.inclusive(ExactRatio.of(least)), state.box().leastOf(atom),
                        "least of " + atom + " over " + written);
                assertEquals(ExactCut.inclusive(ExactRatio.of(most)), state.box().mostOf(atom),
                        "most of " + atom + " over " + written);
            }
            assertTrue(state.isSettledAndComposed(), written.toString());
        }
        // The drawn rules are the shape the basis is for, so every one of them is chosen, and some
        // of them leave nothing and some leave something.
        assertEquals(cases, chosen);
        assertTrue(empty >= 1 && empty < chosen, "empty " + empty + " of " + chosen);
    }

    @Test
    void aFormThatIsOneCoordinateOrADifferenceIsAnsweredByWhatThePointsReach() {
        Random random = new Random(1031);
        int answered = 0;
        for (int round = 0; round < 400; round++) {
            List<String> atoms = ATOMS.subList(0, 2 + random.nextInt(3));
            List<Written> written = PrefixChains.chain(random, atoms.size());
            if (holdsNever(written)) {
                continue;
            }
            List<AffineConstraint<String>> rules = stated(written);
            List<Map<String, Integer>> points = pointsSatisfying(written, atoms, -REACH, REACH);
            ClosedState<String> state = closed(rules, SPELLED);
            if (points.isEmpty() || state.holdsNothing()) {
                continue;
            }
            for (Map<String, ExactRatio> coefs : formsOver(random, atoms)) {
                Highest highest = state.highestInBasis(coefs, ExactRatio.ZERO);
                if (highest instanceof Highest.NotAnswered) {
                    continue;
                }
                answered++;
                long most = points.stream().mapToLong(point -> valueAt(coefs, point)).max()
                        .orElseThrow();
                assertEquals(new Highest.Within(ExactCut.inclusive(ExactRatio.of(most))), highest,
                        coefs + " over " + written);
            }
        }
        assertTrue(answered > 400, "answered " + answered);
    }

    /** A prefix sum, one position either way, and the difference of the first two. */
    private static List<Map<String, ExactRatio>> formsOver(Random random, List<String> atoms) {
        List<Map<String, ExactRatio>> out = new ArrayList<>();
        Map<String, ExactRatio> sum = new LinkedHashMap<>();
        int length = 1 + random.nextInt(atoms.size());
        for (int at = 0; at < length; at++) {
            sum.put(atoms.get(at), ExactRatio.ONE);
        }
        out.add(sum);
        String one = atoms.get(random.nextInt(atoms.size()));
        out.add(Map.of(one, ExactRatio.ONE));
        out.add(Map.of(one, ExactRatio.ONE.negated()));
        Map<String, ExactRatio> difference = new LinkedHashMap<>();
        difference.put(atoms.get(0), ExactRatio.ONE);
        difference.put(atoms.get(1), ExactRatio.ONE.negated());
        out.add(difference);
        return out;
    }

    private static long valueAt(Map<String, ExactRatio> coefs, Map<String, Integer> point) {
        long sum = 0;
        for (Map.Entry<String, ExactRatio> each : coefs.entrySet()) {
            sum += each.getValue().equals(ExactRatio.ONE) ? point.get(each.getKey())
                    : -point.get(each.getKey());
        }
        return sum;
    }

    @Test
    void theStateIsNeverWiderThanTheRulesReadAsTheyAreStated() {
        Random random = new Random(77);
        int compared = 0;
        for (int round = 0; round < 400; round++) {
            List<String> atoms = ATOMS.subList(0, 2 + random.nextInt(3));
            List<Written> written = PrefixChains.chain(random, atoms.size());
            if (holdsNever(written)) {
                continue;
            }
            List<AffineConstraint<String>> rules = stated(written);
            // An equality over a position the others do not name is a rule that is not a half-space,
            // which keeps the basis from being chosen and leaves the rest as they are stated.
            List<Written> beside = new ArrayList<>(written);
            beside.add(rule("z = 0"));
            List<AffineConstraint<String>> asStated = stated(beside);
            assertNull(basisOver(asStated));
            ClosedState<String> basis = closed(rules, SPELLED);
            ClosedState<String> plain = closed(asStated, SPELLED);
            if (plain.holdsNothing()) {
                assertTrue(basis.holdsNothing(), written.toString());
                continue;
            }
            if (basis.holdsNothing()) {
                continue;
            }
            compared++;
            for (String atom : atoms) {
                ExactCut wasLeast = plain.box().leastOf(atom);
                ExactCut wasMost = plain.box().mostOf(atom);
                if (wasLeast != null) {
                    ExactCut least = basis.box().leastOf(atom);
                    assertNotNull(least, atom + " of " + written);
                    assertEquals(least, ExactCut.tighterLower(least, wasLeast),
                            atom + " of " + written);
                }
                if (wasMost != null) {
                    ExactCut most = basis.box().mostOf(atom);
                    assertNotNull(most, atom + " of " + written);
                    assertEquals(most, ExactCut.tighterUpper(most, wasMost),
                            atom + " of " + written);
                }
            }
        }
        assertTrue(compared > 100, "compared " + compared);
    }

    @Test
    void whichPositionOfTheFirstPrefixComesFirstChangesNothing() {
        Random random = new Random(5);
        CanonicalOrder<String> backwards = (one, other) -> other.compareTo(one);
        for (int round = 0; round < 300; round++) {
            List<Written> written = PrefixChains.chain(random, 2 + random.nextInt(3));
            if (holdsNever(written)) {
                continue;
            }
            List<AffineConstraint<String>> rules = stated(written);
            List<AffineConstraint<String>> shuffled = new ArrayList<>(rules);
            Collections.shuffle(shuffled, random);
            ClosedState<String> one = closed(rules, SPELLED);
            ClosedState<String> other = closed(shuffled, backwards);
            assertEquals(one.holdsNothing(), other.holdsNothing(), written.toString());
            if (!one.holdsNothing()) {
                assertEquals(one.box(), other.box(), written.toString());
            }
        }
    }

    @Test
    void rulesThatAreNotSumsOfOnePrefixHaveNoBasis() {
        // Not nested: the second sum leaves the first one's positions out.
        assertNoBasis("a + b <= 3", "b + c <= 3", "a >= 0", "b >= 0", "c >= 0");
        // A position in no sum.
        assertNoBasis("a + b <= 3", "c <= 3");
        // A weighted sum is not one coordinate or the difference of two there.
        assertNoBasis("2a + b <= 3", "a + b + c <= 4");
        // An equality is not a half-space.
        assertNoBasis("a + b = 3", "a + b + c <= 4");
        // A hole is not a half-space either.
        assertNoBasis("a + b <= 3", "a /= 1");
    }

    private static void assertNoBasis(String... texts) {
        List<Written> written = new ArrayList<>();
        for (String text : texts) {
            written.add(rule(text));
        }
        assertNull(basisOver(stated(written)), written.toString());
    }

    private static Granularity filling(String ignored) {
        return Granularity.DENSE;
    }

    @Test
    void positionsThatAreNotWholeNumbersHaveNoBasis() {
        List<AffineConstraint<String>> rules = statedOnly(
                List.of(rule("a + b <= 3"), rule("a + b + c <= 4")),
                APrefixBasisLeavesExactlyWhatTheWholeNumberRulesLeaveTest::filling);

        assertNull(PrefixBasis.over(rules,
                APrefixBasisLeavesExactlyWhatTheWholeNumberRulesLeaveTest::filling, SPELLED));
    }

    /**
     * A closure that could not sum a hop leaves less than the rules do, and a basis is a way of
     * closing them faster and not a way of leaving less. Here the bound on a + b is so far from the
     * one a difference puts beside it in scale that the two have no sum, so there is no basis and
     * the rules are closed as they are stated.
     */
    @Test
    void aClosureThatCouldNotSumAHopHasNoBasis() {
        List<Written> written = List.of(rule("a <= 1"),
                new Written(Map.of("a", ExactRatio.ONE, "b", ExactRatio.ONE), HUGE.negated(),
                        Rel.LE),
                rule("b >= -3"));
        List<AffineConstraint<String>> rules = stated(written);

        assertEquals(3, rules.size());
        assertNull(basisOver(rules));
        ClosedState<String> state = closed(rules, SPELLED);
        assertEquals(ExactCut.inclusive(ExactRatio.ONE), state.box().mostOf("a"));
        assertSame(Highest.NOT_ANSWERED, state.highestInBasis(Map.of("a", ExactRatio.ONE),
                ExactRatio.ZERO));
    }

    /**
     * That nothing bounds a form and that what it comes to cannot be summed are two answers. The
     * first is the basis's, and the second is the rules as they are stated being asked.
     */
    @Test
    void aFormTheArithmeticCannotSumIsNotAnsweredAndIsNotAnsweredAsUnbounded() {
        List<AffineConstraint<String>> bounded = stated(List.of(rule("a >= 0"), rule("a <= 5"),
                rule("b >= 0"), rule("b <= 5"), rule("a + b <= 7")));
        ClosedState<String> state = closed(bounded, SPELLED);

        assertNotNull(basisOver(bounded));
        assertEquals(new Highest.Within(ExactCut.inclusive(ExactRatio.of(5))),
                state.highestInBasis(Map.of("a", ExactRatio.ONE), ExactRatio.ZERO));
        assertSame(Highest.NOT_ANSWERED,
                state.highestInBasis(Map.of("a", ExactRatio.ONE), HUGE));

        List<AffineConstraint<String>> open = stated(List.of(rule("a >= 0"), rule("b >= 0"),
                rule("a + b >= 1")));
        ClosedState<String> unbounded = closed(open, SPELLED);

        assertNotNull(basisOver(open));
        assertInstanceOf(Highest.Unbounded.class,
                unbounded.highestInBasis(Map.of("a", ExactRatio.ONE), ExactRatio.ZERO));
        assertNull(unbounded.box().mostOf("a"));
    }

    @Test
    void aStateNotClosedInABasisAnswersNothingOfAForm() {
        List<AffineConstraint<String>> rules = stated(List.of(rule("a + b <= 3"), rule("a /= 1")));

        assertSame(Highest.NOT_ANSWERED,
                closed(rules, SPELLED).highestInBasis(Map.of("a", ExactRatio.ONE), ExactRatio.ZERO));
    }
}
