package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;
import souther.compiler.numeric.NumericDomain.Rel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The rules are worked out once, and what comes out is a function of the rules.
 *
 * <p>Not of the order they arrived in, not of how many times each was said, and not of whether a
 * rule happened to be written as a difference or as a sum. That last one is the reason the
 * differences are closed again after every round rather than once at the start.
 *
 * <p>Checked against the points over a bounded range, in the one direction that matters: no point
 * the rules admit is left outside what the state says, and where the state says nothing is left,
 * nothing is.
 */
class OneStateAnswersForWhatTheRulesLeaveTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int LOW = -4;
    private static final int HIGH = 4;
    private static final int CASES = 300;

    private record Written(Map<String, Rational> coefs, Rational constant, Rel rel) {}

    private static Rational num(long whole) {
        return Rational.of(whole);
    }

    private static Map<String, Rational> weighing(Object... pairs) {
        Map<String, Rational> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], num((Integer) pairs[i + 1]));
        }
        return out;
    }


    /** The constraint {@code read} states, where it states one. Asked through the reading's own
     *  type, so that what comes back is a constraint over the same positions the reading was of. */
    private static AffineConstraint<String> stated(Read<String> read) {
        assertInstanceOf(Read.Stated.class, read);
        return ((Read.Stated<String>) read).constraint();
    }

    private static AffineConstraint<String> rule(Map<String, Rational> coefs, long constant,
                                                 Rel rel) {
        return stated(AffineConstraint.of(coefs, num(constant), rel,
                atom -> Granularity.DISCRETE));
    }

    private static ClosedState<String> closing(List<AffineConstraint<String>> rules) {
        return ClosedState.of(rules, atom -> Granularity.DISCRETE);
    }

    // --- the issue, end to end --------------------------------------------------------------------

    /**
     * A rule over more than one position now narrows the positions it names. Under the issue's own
     * numbers the rule is not the binding one; under wider own-bounds it is, and it says so.
     */
    @Test
    void aRuleOverSeveralPositionsNarrowsThePositionsItNames() {
        ClosedState<String> closed = closing(List.of(
                rule(weighing("straw", 1), 0, Rel.GE),
                rule(weighing("straw", 1), -1000, Rel.LE),
                rule(weighing("choco", 1), 0, Rel.GE),
                rule(weighing("choco", 1), -6, Rel.LE),
                rule(weighing("straw", 300, "choco", 600), -4800, Rel.LE)));

        assertEquals(RationalCut.inclusive(num(16)), closed.box().mostOf("straw"));
        assertEquals(RationalCut.inclusive(num(6)), closed.box().mostOf("choco"),
                "its own rule is the tighter one here and stays");
    }

    /** And where its own bound is tighter, the position keeps it. */
    @Test
    void thePositionKeepsWhicheverBoundIsTighter() {
        ClosedState<String> closed = closing(List.of(
                rule(weighing("straw", 1), 0, Rel.GE),
                rule(weighing("straw", 1), -10, Rel.LE),
                rule(weighing("choco", 1), 0, Rel.GE),
                rule(weighing("straw", 300, "choco", 600), -4800, Rel.LE)));
        assertEquals(RationalCut.inclusive(num(10)), closed.box().mostOf("straw"));
    }

    /**
     * A bound a sum found on one position reaches every position held against it, however long the
     * chain of differences between them.
     *
     * <p>The chain is built longer than the rounds are, on purpose. Read one rule at a time against
     * the box, a bound walks one link of a chain per round and a chain longer than the budget never
     * arrives; carried along the closed differences it arrives in one step whatever the length. So
     * this is the case that tells the two apart, and it stays the case if the budget changes.
     */
    @Test
    void aBoundReachesTheFarEndOfAChainLongerThanTheRounds() {
        int links = ClosedState.ROUNDS + 4;
        List<AffineConstraint<String>> rules = new ArrayList<>();
        for (int i = 0; i < links; i++) {
            rules.add(rule(weighing("x" + i, 1, "x" + (i + 1), -1), 0, Rel.LE));
        }
        rules.add(rule(weighing("y", 1), 0, Rel.GE));
        rules.add(rule(weighing("x" + links, 3, "y", 2), -12, Rel.LE));   // the far end is under four

        ClosedState<String> closed = closing(rules);
        assertEquals(RationalCut.inclusive(num(4)), closed.box().mostOf("x" + links));
        assertEquals(RationalCut.inclusive(num(4)), closed.box().mostOf("x0"),
                "and the near end is under it too, " + links + " links away");
    }

    /**
     * A round reads what the round before it left.
     *
     * <p>Every rule in a round reads the same box, so what one of them finds is not available to
     * another until the next round. Here the first round can only learn that {@code b} is at least
     * two, and it takes a second for that to bear on {@code a}.
     */
    @Test
    void aRoundReadsWhatTheRoundBeforeItLeft() {
        ClosedState<String> closed = closing(List.of(
                rule(weighing("a", 1), 0, Rel.GE),
                rule(weighing("b", 1), 0, Rel.GE),
                rule(weighing("c", 1), 0, Rel.GE),
                rule(weighing("c", 1), -5, Rel.LE),
                rule(weighing("b", 2, "c", -1), -4, Rel.GE),      // first round: b >= 2
                rule(weighing("a", 1, "b", 3), -20, Rel.LE)));    // second round: a <= 14

        assertEquals(RationalCut.inclusive(num(2)), closed.box().leastOf("b"));
        assertEquals(RationalCut.inclusive(num(14)), closed.box().mostOf("a"),
                "which one round cannot say, since it reads b at nought or above");
    }

    // --- emptiness ---------------------------------------------------------------------------------

    @Test
    void aSumThatLeavesNothingIsFoundThoughNoDifferenceIsWrong() {
        ClosedState<String> closed = closing(List.of(
                rule(weighing("a", 1), -10, Rel.GE),
                rule(weighing("b", 1), -10, Rel.GE),
                rule(weighing("a", 1, "b", 1), -5, Rel.LE)));
        assertTrue(closed.holdsNothing());
        assertThrows(IllegalStateException.class, closed::box);
    }

    /** Over decimals `3a` never comes to one, so this is a rule nothing satisfies — and it is
     *  settled when the rule is read rather than by anything the state does. */
    @Test
    void aRuleAtAValueItsSumCannotReachLeavesNothing() {
        Read<String> read = AffineConstraint.of(Map.of("a", num(3)), num(-1), Rel.EQ,
                atom -> Granularity.DENSE);
        assertInstanceOf(Read.HoldsNever.class, read);
    }

    // --- the same rules, the same answer ------------------------------------------------------------

    @Test
    void theOrderTheRulesArrivedInIsNotPartOfTheAnswer() {
        Random dice = new Random(891);
        for (int round = 0; round < CASES; round++) {
            List<AffineConstraint<String>> stated = read(someRules(dice));
            List<AffineConstraint<String>> shuffled = new ArrayList<>(stated);
            Collections.shuffle(shuffled, dice);

            ClosedState<String> asWritten = closing(stated);
            ClosedState<String> reordered = closing(shuffled);
            assertEquals(asWritten.holdsNothing(), reordered.holdsNothing(),
                    () -> "emptiness moved when the rules were reordered: " + stated);
            if (asWritten.holdsNothing()) {
                continue;
            }
            assertEquals(asWritten.box(), reordered.box(),
                    () -> "the box moved when the rules were reordered: " + stated);
        }
    }

    @Test
    void sayingARuleTwiceSaysWhatSayingItOnceSays() {
        Random dice = new Random(1016);
        for (int round = 0; round < CASES; round++) {
            List<AffineConstraint<String>> stated = read(someRules(dice));
            List<AffineConstraint<String>> doubled = new ArrayList<>(stated);
            doubled.addAll(stated);
            ClosedState<String> once = closing(stated);
            ClosedState<String> twice = closing(doubled);
            assertEquals(once.holdsNothing(), twice.holdsNothing());
            if (!once.holdsNothing()) {
                assertEquals(once.box(), twice.box());
            }
        }
    }

    // --- against the points -------------------------------------------------------------------------

    @Test
    void noPointTheRulesAdmitIsEverRefused() {
        Random dice = new Random(4800);
        int narrowed = 0;
        int empties = 0;
        for (int round = 0; round < CASES; round++) {
            List<Written> written = someRules(dice);
            List<AffineConstraint<String>> stated = read(written);
            // Every position bounded to the range, so the points enumerated are all the points.
            for (String position : POSITIONS) {
                stated.add(rule(weighing(position, 1), -LOW, Rel.GE));
                stated.add(rule(weighing(position, 1), -HIGH, Rel.LE));
            }
            List<Map<String, Integer>> admitted = pointsSatisfying(written);
            ClosedState<String> closed = closing(stated);

            if (admitted.isEmpty()) {
                empties++;
                continue;   // emptiness is proven one way only, so nothing is owed here
            }
            assertFalse(closed.holdsNothing(),
                    () -> "said nothing is left, but " + written + " admits " + admitted.size());
            for (Map<String, Integer> point : admitted) {
                for (String position : POSITIONS) {
                    Rational at = num(point.get(position));
                    assertTrue(admits(closed.box().leastOf(position), at, false)
                                    && admits(closed.box().mostOf(position), at, true),
                            () -> "refused a point the rules admit: " + point + " under " + written
                                    + " left " + position + " in ["
                                    + closed.box().leastOf(position) + ", "
                                    + closed.box().mostOf(position) + "]");
                }
            }
            for (String position : POSITIONS) {
                int most = admitted.stream().mapToInt(p -> p.get(position)).max().orElseThrow();
                if (closed.box().mostOf(position) != null
                        && closed.box().mostOf(position).at().compareTo(num(HIGH)) < 0) {
                    narrowed++;
                }
                assertTrue(most <= HIGH);
            }
        }
        assertTrue(narrowed > 0 && empties > 0,
                "narrowed " + narrowed + " and " + empties + " were empty, so this checked little");
    }

    private static boolean admits(RationalCut cut, Rational value, boolean above) {
        if (cut == null) {
            return true;
        }
        int order = value.compareTo(cut.at());
        return above ? (order < 0 || (order == 0 && cut.inclusive()))
                : (order > 0 || (order == 0 && cut.inclusive()));
    }

    private static List<Written> someRules(Random dice) {
        List<Written> out = new ArrayList<>();
        int howMany = 1 + dice.nextInt(3);
        for (int i = 0; i < howMany; i++) {
            Map<String, Rational> coefs = new LinkedHashMap<>();
            for (String position : POSITIONS) {
                int weight = dice.nextInt(5) - 2;
                if (weight != 0) {
                    coefs.put(position, num(weight));
                }
            }
            if (coefs.isEmpty()) {
                continue;
            }
            out.add(new Written(coefs, num(dice.nextInt(15) - 7), someRelation(dice)));
        }
        return out;
    }


    /**
     * One of the relations a rule can be written with, taken from the enum rather than from a list.
     *
     * <p>Written out, this was a copy of {@link Rel} that nothing compared against it, and the
     * {@code default} arm meant it went on compiling however far the two drifted. They did: one
     * generator here left out {@code /=} and the one beside it left out {@code /=} and {@code >},
     * so the properties these tests hold — sound against the points, the same whatever order the
     * rules arrived in, never wider for a narrower box — were never asked of a rule of that shape.
     * The reading that decides which side of a hole a sum falls went unchecked by all three.
     *
     * <p>Taken from the values, a relation added to the language is generated here without anyone
     * remembering to add it.
     */
    private static Rel someRelation(Random dice) {
        Rel[] all = Rel.values();
        return all[dice.nextInt(all.length)];
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (Written each : written) {
            if (AffineConstraint.of(each.coefs(), each.constant(), each.rel(),
                    atom -> Granularity.DISCRETE) instanceof Read.Stated<String> stated) {
                out.add(stated.constraint());
            }
        }
        return out;
    }

    private static List<Map<String, Integer>> pointsSatisfying(List<Written> written) {
        List<Map<String, Integer>> out = new ArrayList<>();
        for (int a = LOW; a <= HIGH; a++) {
            for (int b = LOW; b <= HIGH; b++) {
                for (int c = LOW; c <= HIGH; c++) {
                    Map<String, Integer> point = new LinkedHashMap<>();
                    point.put("a", a);
                    point.put("b", b);
                    point.put("c", c);
                    if (written.stream().allMatch(rule -> holdsAt(rule, point))) {
                        out.add(point);
                    }
                }
            }
        }
        return out;
    }

    private static boolean holdsAt(Written rule, Map<String, Integer> point) {
        Rational total = rule.constant();
        for (Map.Entry<String, Rational> each : rule.coefs().entrySet()) {
            total = total.plus(each.getValue().times(num(point.get(each.getKey()))));
        }
        int sign = total.signum();
        return switch (rule.rel()) {
            case LE -> sign <= 0;
            case LT -> sign < 0;
            case GE -> sign >= 0;
            case GT -> sign > 0;
            case EQ -> sign == 0;
            case NE -> sign != 0;
        };
    }
}
