package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.RulesAsWritten.Written;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
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
 * is not a half-space keeps the basis from being chosen), and which position of the first prefix
 * is taken first does not change what any position is left.
 */
class APrefixBasisLeavesExactlyWhatTheWholeNumberRulesLeaveTest {

    private static final List<String> ATOMS = List.of("a", "b", "c", "d");
    private static final Function<String, Granularity> WHOLE = _ -> Granularity.DISCRETE;
    private static final CanonicalOrder<String> SPELLED = CanonicalOrder.asTheyAreSpelled();
    private static final CanonicalOrder<String> BACKWARDS = (one, other) -> other.compareTo(one);
    private static final int REACH = 5;

    private static final List<String> RELATIONS = List.of("<=", "<", ">=", ">");

    /** Each atom boxed within the reach, and a bound or two on each prefix sum of two atoms or more. */
    private static List<Written> chain(Random random, List<String> atoms) {
        List<Written> out = new ArrayList<>();
        for (String atom : atoms) {
            out.add(rule(atom + " >= " + (-REACH + random.nextInt(4))));
            out.add(rule(atom + " <= " + (REACH - random.nextInt(4))));
        }
        StringBuilder prefix = new StringBuilder(atoms.getFirst());
        for (int at = 1; at < atoms.size(); at++) {
            prefix.append(" + ").append(atoms.get(at));
            boolean bounded = false;
            for (String relation : RELATIONS) {
                if (random.nextInt(4) == 0) {
                    out.add(rule(prefix + " " + relation + " " + (random.nextInt(15) - 7)));
                    bounded = true;
                }
            }
            if (!bounded) {
                out.add(rule(prefix + " " + RELATIONS.get(random.nextInt(4)) + " "
                        + (random.nextInt(15) - 7)));
            }
        }
        return out;
    }

    @Test
    void theBoxIsWhatThePointsLeaveEachPosition() {
        Random random = new Random(3167);
        int chosen = 0;
        int cases = 0;
        int empty = 0;
        for (int round = 0; round < 600; round++) {
            List<String> atoms = ATOMS.subList(0, 2 + random.nextInt(3));
            List<Written> written = chain(random, atoms);
            if (someRuleHoldsNever(written, WHOLE)) {
                continue;
            }
            List<AffineConstraint<String>> rules = statedOnly(written, WHOLE);
            cases++;
            if (PrefixBasis.over(rules, WHOLE, SPELLED) == null) {
                continue;
            }
            chosen++;
            ClosedState<String> state = ClosedState.closedTogether(rules, WHOLE, SPELLED);
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
            List<Written> written = chain(random, atoms);
            if (someRuleHoldsNever(written, WHOLE)) {
                continue;
            }
            List<AffineConstraint<String>> rules = statedOnly(written, WHOLE);
            List<Map<String, Integer>> points = pointsSatisfying(written, atoms, -REACH, REACH);
            ClosedState<String> state = ClosedState.closedTogether(rules, WHOLE, SPELLED);
            if (points.isEmpty() || state.holdsNothing()) {
                continue;
            }
            for (Map<String, ExactRatio> coefs : formsOver(random, atoms)) {
                PrefixBasis.Highest highest = state.highestInBasis(coefs, ExactRatio.ZERO);
                if (highest == null) {
                    continue;
                }
                answered++;
                long most = points.stream().mapToLong(point -> valueAt(coefs, point)).max()
                        .orElseThrow();
                assertEquals(ExactCut.inclusive(ExactRatio.of(most)), highest.at(),
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
            List<Written> written = chain(random, atoms);
            if (someRuleHoldsNever(written, WHOLE)) {
                continue;
            }
            List<AffineConstraint<String>> rules = statedOnly(written, WHOLE);
            // An equality over a position the others do not name is a rule that is not a half-space,
            // which keeps the basis from being chosen and leaves the rest as they are stated.
            List<Written> beside = new ArrayList<>(written);
            beside.add(rule("z = 0"));
            List<AffineConstraint<String>> asStated = statedOnly(beside, WHOLE);
            assertNull(PrefixBasis.over(asStated, WHOLE, SPELLED));
            ClosedState<String> basis = ClosedState.closedTogether(rules, WHOLE, SPELLED);
            ClosedState<String> plain = ClosedState.closedTogether(asStated, WHOLE, SPELLED);
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
        for (int round = 0; round < 300; round++) {
            List<String> atoms = ATOMS.subList(0, 2 + random.nextInt(3));
            List<Written> written = chain(random, atoms);
            if (someRuleHoldsNever(written, WHOLE)) {
                continue;
            }
            List<AffineConstraint<String>> rules = statedOnly(written, WHOLE);
            List<AffineConstraint<String>> shuffled = new ArrayList<>(rules);
            Collections.shuffle(shuffled, random);
            ClosedState<String> one = ClosedState.closedTogether(rules, WHOLE, SPELLED);
            ClosedState<String> other = ClosedState.closedTogether(shuffled, WHOLE, BACKWARDS);
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
        assertNull(PrefixBasis.over(statedOnly(written, WHOLE), WHOLE, SPELLED),
                written.toString());
    }

    @Test
    void positionsThatAreNotWholeNumbersHaveNoBasis() {
        Function<String, Granularity> dense = _ -> Granularity.DENSE;
        List<AffineConstraint<String>> rules = statedOnly(
                List.of(rule("a + b <= 3"), rule("a + b + c <= 4")), dense);
        assertNull(PrefixBasis.over(rules, dense, SPELLED));
    }
}
