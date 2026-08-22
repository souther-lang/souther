package souther.compiler.numeric;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule over several positions is narrowed against everything the state holds, and not against each
 * position's own ends alone.
 *
 * <p>The rest of a rule is a sum, and what bounds a sum is often no position's own end. Under
 * {@code guard x >= y} neither {@code x} nor {@code y} is bounded at all, while {@code x - y} is
 * bounded at nought — so a rule relating that sum to a third position was left deriving nothing,
 * while the goal side, asking the very same question of the very same state, read the relation and
 * answered. Which of the two an author's program reached decided whether a construction was
 * discharged.
 *
 * <p>Small and stated, rather than searched for. The properties a reduction promises — sound against
 * the points, the same whatever order the rules arrived in, never wider for a narrower box — are
 * held by {@link ARuleOverSeveralPositionsNarrowsEachOfThemTest} and
 * {@link OneStateAnswersForWhatTheRulesLeaveTest}, which read this route already.
 */
class ARulesRestIsBoundedByRelationsAndNotOnlyByEndsTest {

    private static final Map<String, Granularity> WHOLE = Map.of(
            "x", Granularity.DISCRETE, "y", Granularity.DISCRETE, "z", Granularity.DISCRETE);

    private static LinearForm<String> form(Object... parts) {
        Map<String, BigDecimal> coefs = new LinkedHashMap<>();
        BigDecimal constant = BigDecimal.ZERO;
        for (int i = 0; i < parts.length; i += 2) {
            BigDecimal weight = BigDecimal.valueOf(((Number) parts[i + 1]).longValue());
            if (parts[i] == null) {
                constant = weight;
            } else {
                coefs.put((String) parts[i], weight);
            }
        }
        return new LinearForm<>(constant, coefs);
    }

    /**
     * The shape the issue's model comes to.
     *
     * <p>{@code 額 - 十 * 10 == 0} taken with a guard that put {@code 額} at or above nought, where
     * {@code 額} is the argument {@code 合計金額(投入) - 値段} read through the helper's parameter. Ten
     * counts of a coin is what is left of a sum, and the sum is bounded by the guard and by neither
     * of its two positions.
     */
    @Test
    void aPositionIsBoundedByARelationOverTheRestOfItsRule() {
        NumericDomain<String> rules = NumericDomain.<String>top()
                .assume(form("z", 10, "x", -1, "y", 1), Rel.EQ, WHOLE)
                .assume(form("x", 1, "y", -1), Rel.GE, WHOLE);

        assertTrue(rules.entails(form("z", 1), Rel.GE),
                "10z = x - y with x - y at or above nought puts z at or above nought");
        assertEquals(BigDecimal.ZERO, Count.number(rules.boundsOf("z").min().at()).at());
    }

    /**
     * And the ends alone do not reach it, which is what says the relation is what did.
     *
     * <p>The same rule with the relation dropped. Nothing bounds {@code x} or {@code y}, so nothing
     * bounds {@code z} — a control for the case above rather than a rule anybody wants.
     */
    @Test
    void withoutTheRelationTheSameRuleBoundsNothing() {
        NumericDomain<String> rules = NumericDomain.<String>top()
                .assume(form("z", 10, "x", -1, "y", 1), Rel.EQ, WHOLE);

        assertFalse(rules.entails(form("z", 1), Rel.GE));
        assertNull(rules.boundsOf("z").min());
    }

    /**
     * A relation the closed differences hold is not the whole of it.
     *
     * <p>{@code 10x - y >= 0} is not a difference — its positions are weighed ten and minus one — so
     * the difference bounds hold nothing about it and it is a rule like any other. It bounds the rest
     * of the rule beside it all the same, which is the half of this that reading the differences
     * alone does not answer.
     */
    @Test
    void aRelationTheDifferencesCannotHoldBoundsTheRestAsWell() {
        NumericDomain<String> rules = NumericDomain.<String>top()
                .assume(form("z", 10, "x", -10, "y", 1), Rel.EQ, WHOLE)
                .assume(form("x", 10, "y", -1), Rel.GE, WHOLE);

        assertTrue(rules.entails(form("z", 1), Rel.GE),
                "10z = 10x - y with 10x - y at or above nought puts z at or above nought");
    }

    /**
     * A chain of rules composes through the rounds, which is what it did before this and still does.
     *
     * <p>Said here beside the change because the change is easy to mistake for it: a reading composes
     * at most one other rule, and three rules still reach an answer no two of them do, by way of the
     * ends each round hands the next.
     */
    @Test
    void aChainOfRulesStillComposesThroughTheRounds() {
        NumericDomain<String> rules = NumericDomain.<String>top()
                .assume(form("x", 2, "y", -1), Rel.GE, WHOLE)
                .assume(form("y", 2, "z", -1), Rel.GE, WHOLE)
                .assume(form("z", 1, null, -40), Rel.GE, WHOLE);

        Bounds y = rules.boundsOf("y");
        Bounds x = rules.boundsOf("x");
        assertNotNull(y.min());
        assertNotNull(x.min());
        assertEquals(BigDecimal.valueOf(20), Count.number(y.min().at()).at());
        assertEquals(BigDecimal.valueOf(10), Count.number(x.min().at()).at());
    }

    /**
     * A rule is not among the rules read for a bound on the rest of itself.
     *
     * <p>One rule and nothing else, and one of a shape the difference bounds do not hold — weighed
     * ten and minus one — so the rule route is the only route that could answer. Asked plainly it
     * does answer, which is the control; asked as that rule's own rest it does not.
     *
     * <p>Not a soundness measure: a rule is a sound premise for a bound on its own rest, and letting
     * it in was measured to move nothing. It is left out so that no bound rests on the rule it is a
     * bound on.
     *
     * <p>What is left out is the rule, and not what the closure made of it. A rule of difference
     * shape has been read into the closed differences, which are the state and are no longer any one
     * rule's — so such a rule still bounds its own rest by that route, as it did before this and for
     * the same reason {@link ClosedState} carries the box along the differences after every round.
     */
    @Test
    void aRuleIsNotReadForABoundOnTheRestOfItself() {
        AffineConstraint<String> rule = stated(form("x", 10, "y", -1), Rel.GE);
        List<AffineConstraint<String>> alone = List.of(rule);
        FormReach<String> reading = FormReach.over(alone, Box.unbounded(),
                DifferenceBounds.over(alone));
        Map<String, Rational> itsOwnForm = Map.of("x", Rational.of(10), "y", Rational.of(-1));

        assertNotNull(reading.of(itsOwnForm, Rational.ZERO).least(),
                "the rule bounds 10x - y below, so reading it plainly says so");
        assertNull(reading.ofTheRestOf(rule, itsOwnForm, Rational.ZERO).least(),
                "and reading it as that rule's own rest does not");
    }

    private static AffineConstraint<String> stated(LinearForm<String> f, Rel rel) {
        Map<String, Rational> coefs = new LinkedHashMap<>();
        f.coefs().forEach((position, weight) -> coefs.put(position, Rational.of(weight)));
        AffineConstraint.Read<String> read = AffineConstraint.of(coefs,
                Rational.of(f.constant()), rel, position -> Granularity.DISCRETE);
        return ((AffineConstraint.Read.Stated<String>) read).constraint();
    }
}
