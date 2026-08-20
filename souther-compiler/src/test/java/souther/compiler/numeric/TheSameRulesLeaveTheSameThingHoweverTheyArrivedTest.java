package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a domain says is a function of the rules it was given, and of nothing else.
 *
 * <p>Not of the order they arrived in. That had not been true, and it was not the diagnostics that
 * moved but the answer itself — measured on this domain before any of this was written:
 *
 * <pre>
 *     x /= 0 ; x &gt;= 0  left x in [0, ∞)
 *     x &gt;= 0 ; x /= 0  left x in [1, ∞)
 * </pre>
 *
 * <p>Two rules, two orders, two ranges, and the first of them admits a value the rules refuse. The
 * cause was that a disequality was turned into a bound using whatever happened to be known at the
 * moment it was read, and never looked at again.
 *
 * <p>Nor of how many times each rule was said. A rule written twice is one rule.
 */
class TheSameRulesLeaveTheSameThingHoweverTheyArrivedTest {

    private record Written(LinearForm<String> form, Rel rel) {}

    private static LinearForm<String> atom(String a) {
        return LinearForm.atom(a);
    }

    private static LinearForm<String> num(long n) {
        return LinearForm.constant(BigDecimal.valueOf(n));
    }

    private static LinearForm<String> scaled(String a, long k) {
        return LinearForm.<String>atom(a).times(BigDecimal.valueOf(k));
    }

    private static Map<String, Granularity> whole(String... atoms) {
        Map<String, Granularity> out = new LinkedHashMap<>();
        for (String each : atoms) {
            out.put(each, Granularity.DISCRETE);
        }
        return out;
    }

    private static NumericDomain<String> given(List<Written> rules, Map<String, Granularity> kinds) {
        NumericDomain<String> out = NumericDomain.top();
        for (Written each : rules) {
            out = out.assume(each.form(), each.rel(), kinds);
        }
        return out;
    }

    // --- the case that was measured -----------------------------------------------------------------

    @Test
    void aHoleAndABoundLeaveTheSameThingWhicheverWasWrittenFirst() {
        Map<String, Granularity> kinds = whole("x");
        Written hole = new Written(atom("x"), Rel.NE);
        Written floor = new Written(atom("x"), Rel.GE);

        Bounds holeFirst = given(List.of(hole, floor), kinds).boundsOf("x");
        Bounds floorFirst = given(List.of(floor, hole), kinds).boundsOf("x");

        assertEquals(floorFirst, holeFirst, "the same two rules, the other way round");
        assertEquals(Endpoint.inclusive(new Count(BigDecimal.ONE)), holeFirst.min(),
                "and both leave x at one or above, which is what the two rules say together");
    }

    /** The hole is read against everything known and not against what was known at the time, so it
     *  bites when a later rule is what makes it bite. */
    @Test
    void aHoleBitesOnWhatALaterRuleEstablishes() {
        Map<String, Granularity> kinds = whole("x");
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom("x"), Rel.NE, kinds)
                .assume(atom("x").minus(num(5)), Rel.LE, kinds)
                .assume(atom("x"), Rel.GE, kinds);
        assertEquals(Endpoint.inclusive(new Count(BigDecimal.ONE)), d.boundsOf("x").min());
    }

    @Test
    void aHoleWithNothingToSideItStaysAHole() {
        Map<String, Granularity> kinds = whole("x");
        NumericDomain<String> d = NumericDomain.<String>top().assume(atom("x"), Rel.NE, kinds);
        assertTrue(d.boundsOf("x").saysNothing(), "nothing says which side of nought x is on");
        assertFalse(d.isBottom());
    }

    @Test
    void aHoleAtTheOnlyValueLeftLeavesNothing() {
        Map<String, Granularity> kinds = whole("x");
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom("x"), Rel.GE, kinds)
                .assume(atom("x"), Rel.LE, kinds)
                .assume(atom("x"), Rel.NE, kinds);
        assertTrue(d.isBottom(), "x is nought and x is not nought");
    }

    // --- the issue -----------------------------------------------------------------------------------

    /** A rule over more than one position now narrows the positions it names, and the proof knows
     *  what the range knows. */
    @Test
    void aRuleOverTwoPositionsNarrowsThemAndIsProvenFromWhatItLeft() {
        Map<String, Granularity> kinds = whole("straw", "choco");
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom("straw"), Rel.GE, kinds)
                .assume(atom("straw").minus(num(1000)), Rel.LE, kinds)
                .assume(atom("choco"), Rel.GE, kinds)
                .assume(atom("choco").minus(num(6)), Rel.LE, kinds)
                .assume(scaled("straw", 300).plus(scaled("choco", 600)).minus(num(4800)),
                        Rel.LE, kinds);

        assertEquals(Endpoint.inclusive(new Count(BigDecimal.valueOf(16))),
                d.boundsOf("straw").max(), "choco is never below nought");
        assertTrue(d.entails(atom("straw").minus(num(16)), Rel.LE),
                "and the proof says what the range says");
        assertTrue(d.projectionEntails(atom("straw").minus(num(16)), Rel.LE),
                "including what is handed over on its own");
    }

    /** A rule that contradicts the bounds makes the path unreachable, rather than leaving a range
     *  describing a value nobody can build while the proof discharges everything. */
    @Test
    void aRuleThatCannotHoldWithTheBoundsLeavesNothing() {
        Map<String, Granularity> kinds = whole("a", "b");
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(atom("a").minus(num(20)), Rel.GE, kinds)
                .assume(atom("b").minus(num(20)), Rel.GE, kinds)
                .assume(scaled("a", 300).plus(scaled("b", 600)).minus(num(4800)), Rel.LE, kinds);
        assertTrue(d.isBottom());
        assertTrue(d.boundsOf("a").saysNothing(), "and hands over no range at all");
    }

    /** Over decimals `3a` never comes to one, so this is a path nothing reaches — where it used to
     *  come back with a range around a third whose two ends are decimals and a third is not. */
    @Test
    void aRuleAtAValueItsSumCannotReachLeavesNothing() {
        Map<String, Granularity> dense = Map.of("a", Granularity.DENSE);
        NumericDomain<String> d = NumericDomain.<String>top()
                .assume(scaled("a", 3).minus(num(1)), Rel.EQ, dense);
        assertTrue(d.isBottom());
    }

    // --- and over rules drawn at random ---------------------------------------------------------------

    @Test
    void theOrderAndTheRepetitionAreNotPartOfAnyAnswer() {
        Map<String, Granularity> kinds = whole("a", "b", "c");
        Random dice = new Random(891);
        for (int round = 0; round < 300; round++) {
            List<Written> rules = someRules(dice);
            NumericDomain<String> asWritten = given(rules, kinds);

            List<Written> shuffled = new ArrayList<>(rules);
            Collections.shuffle(shuffled, dice);
            NumericDomain<String> reordered = given(shuffled, kinds);

            List<Written> doubled = new ArrayList<>(rules);
            doubled.addAll(rules);
            NumericDomain<String> twice = given(doubled, kinds);

            for (NumericDomain<String> other : List.of(reordered, twice)) {
                assertEquals(asWritten.isBottom(), other.isBottom(),
                        () -> "whether anything is left moved: " + rules);
                for (String position : List.of("a", "b", "c")) {
                    assertEquals(asWritten.boundsOf(position), other.boundsOf(position),
                            () -> "the range at " + position + " moved: " + rules);
                }
                for (Written each : rules) {
                    assertEquals(asWritten.entails(each.form(), each.rel()),
                            other.entails(each.form(), each.rel()),
                            () -> "what is proven moved: " + rules);
                    assertEquals(asWritten.refutes(each.form(), each.rel()),
                            other.refutes(each.form(), each.rel()),
                            () -> "what is refuted moved: " + rules);
                }
            }
        }
    }

    private static List<Written> someRules(Random dice) {
        List<String> positions = List.of("a", "b", "c");
        List<Written> out = new ArrayList<>();
        int howMany = 2 + dice.nextInt(4);
        for (int i = 0; i < howMany; i++) {
            LinearForm<String> form = num(dice.nextInt(15) - 7);
            for (String position : positions) {
                int weight = dice.nextInt(5) - 2;
                if (weight != 0) {
                    form = form.plus(scaled(position, weight));
                }
            }
            if (form.coefs().isEmpty()) {
                continue;
            }
            Rel rel = switch (dice.nextInt(6)) {
                case 0 -> Rel.LT;
                case 1 -> Rel.GE;
                case 2 -> Rel.GT;
                case 3 -> Rel.EQ;
                case 4 -> Rel.NE;
                default -> Rel.LE;
            };
            out.add(new Written(form, rel));
        }
        return out;
    }
}
