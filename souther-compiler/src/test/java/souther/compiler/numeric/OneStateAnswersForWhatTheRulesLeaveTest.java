package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;
import souther.compiler.numeric.RulesAsWritten.Written;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.OVER_THREE;
import static souther.compiler.numeric.RulesAsWritten.admits;
import static souther.compiler.numeric.RulesAsWritten.boxed;
import static souther.compiler.numeric.RulesAsWritten.pointsSatisfying;
import static souther.compiler.numeric.RulesAsWritten.relationsIn;
import static souther.compiler.numeric.RulesAsWritten.rules;
import static souther.compiler.numeric.RulesAsWritten.everyOrder;
import static souther.compiler.numeric.RulesAsWritten.twice;

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
 *
 * <p>Over the systems of {@link RulesAsWritten#OVER_THREE}, each written for a step the closure
 * takes or hands to the reduction: a weighted difference that must not be read as a difference, a
 * cycle summing to nought, ends meeting at one value, a hole sided one way and not the other, a part
 * holding nothing beside one that holds something, and two premises bounding one sum, which a
 * reading letting the later one win answers differently in some order. Each is given in every order
 * its rules have.
 */
class OneStateAnswersForWhatTheRulesLeaveTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int LOW = -4;
    private static final int HIGH = 4;

    private static ExactRatio num(long whole) {
        return ExactRatio.of(whole);
    }

    private static Map<String, ExactRatio> weighing(Object... pairs) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
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

    private static AffineConstraint<String> rule(Map<String, ExactRatio> coefs, long constant,
                                                 Rel rel) {
        return stated(AffineConstraint.of(coefs, num(constant), rel,
                atom -> Granularity.DISCRETE));
    }

    private static ClosedState<String> closing(List<AffineConstraint<String>> rules) {
        return ClosedState.of(rules, atom -> Granularity.DISCRETE,
                CanonicalOrder.asTheyAreSpelled());
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

        assertEquals(ExactCut.inclusive(num(16)), closed.box().mostOf("straw"));
        assertEquals(ExactCut.inclusive(num(6)), closed.box().mostOf("choco"),
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
        assertEquals(ExactCut.inclusive(num(10)), closed.box().mostOf("straw"));
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
        assertEquals(ExactCut.inclusive(num(4)), closed.box().mostOf("x" + links));
        assertEquals(ExactCut.inclusive(num(4)), closed.box().mostOf("x0"),
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

        assertEquals(ExactCut.inclusive(num(2)), closed.box().leastOf("b"));
        assertEquals(ExactCut.inclusive(num(14)), closed.box().mostOf("a"),
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

    /**
     * And a chosen system holding such a rule is refused where it is read, rather than handed on
     * without it. Left out, the points would hold nothing while the state held something, and a
     * check that asks only of the points that are left would pass over the two disagreeing.
     */
    @Test
    void aRuleNoWholeValueSatisfiesIsRefusedWhereTheSystemIsRead() {
        assertThrows(IllegalArgumentException.class, () -> read(rules("2a = 1")));
        assertEquals(List.of(), read(rules("2a /= 1")),
                "a rule every value satisfies states nothing, and is left out");
    }

    // --- the same rules, the same answer ------------------------------------------------------------

    @Test
    void theOrderTheRulesArrivedInIsNotPartOfTheAnswer() {
        for (List<Written> written : OVER_THREE) {
            List<AffineConstraint<String>> stated = read(written);
            ClosedState<String> asWritten = closing(stated);
            for (List<AffineConstraint<String>> order : everyOrder(stated)) {
                ClosedState<String> reordered = closing(order);
                assertEquals(asWritten.holdsNothing(), reordered.holdsNothing(),
                        () -> "emptiness moved when the rules were reordered: " + order);
                if (!asWritten.holdsNothing()) {
                    assertEquals(asWritten.box(), reordered.box(),
                            () -> "the box moved when the rules were reordered: " + order);
                }
            }
        }
    }

    @Test
    void sayingARuleTwiceSaysWhatSayingItOnceSays() {
        for (List<Written> written : OVER_THREE) {
            List<AffineConstraint<String>> stated = read(written);
            ClosedState<String> once = closing(stated);
            ClosedState<String> twice = closing(twice(stated));
            assertEquals(once.holdsNothing(), twice.holdsNothing(), stated::toString);
            if (!once.holdsNothing()) {
                assertEquals(once.box(), twice.box(), stated::toString);
            }
        }
    }

    // --- against the points -------------------------------------------------------------------------

    @Test
    void noPointTheRulesAdmitIsEverRefused() {
        assertEquals(Set.of(Rel.values()), relationsIn(OVER_THREE),
                "a relation no system is written with is one no reading of it is asked about");
        int narrowed = 0;
        int empties = 0;
        for (List<Written> rules : OVER_THREE) {
            // Every position bounded to the range, so the points enumerated are all the points.
            List<Written> written = boxed(rules, POSITIONS, LOW, HIGH);
            List<Map<String, Integer>> admitted = pointsSatisfying(written, POSITIONS, LOW, HIGH);
            ClosedState<String> closed = closing(read(written));

            if (admitted.isEmpty()) {
                empties++;
                continue;   // emptiness is proven one way only, so nothing is owed here
            }
            assertFalse(closed.holdsNothing(),
                    () -> "said nothing is left, but " + written + " admits " + admitted.size());
            // A box holds every admitted point exactly when, at each position, it holds the least
            // and the greatest value an admitted point has there — so those two points are the
            // ones asked about.
            for (String position : POSITIONS) {
                Map<String, Integer> lowest = admitted.getFirst();
                Map<String, Integer> highest = admitted.getFirst();
                for (Map<String, Integer> point : admitted) {
                    if (point.get(position) < lowest.get(position)) {
                        lowest = point;
                    }
                    if (point.get(position) > highest.get(position)) {
                        highest = point;
                    }
                }
                for (Map<String, Integer> point : List.of(lowest, highest)) {
                    ExactRatio at = num(point.get(position));
                    assertTrue(admits(closed.box().leastOf(position), at, false)
                                    && admits(closed.box().mostOf(position), at, true),
                            () -> "refused a point the rules admit: " + point + " under " + written
                                    + " left " + position + " in ["
                                    + closed.box().leastOf(position) + ", "
                                    + closed.box().mostOf(position) + "]");
                }
            }
            for (String position : POSITIONS) {
                if (closed.box().mostOf(position) != null
                        && closed.box().mostOf(position).at().compareTo(num(HIGH)) < 0) {
                    narrowed++;
                }
            }
        }
        assertTrue(narrowed > 0 && empties > 0,
                "narrowed " + narrowed + " and " + empties + " were empty, so this checked little");
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        return RulesAsWritten.read(written, atom -> Granularity.DISCRETE);
    }
}
