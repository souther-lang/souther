package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A closure kept for a question stands for every question equal to it, and for no other.
 *
 * <p>What a closure is worked out from is the rules, the spacing of the positions they weigh, and
 * where the order puts those positions. Each of the three is varied here on its own, and each of
 * them is what decides whether a closure already worked out is lent: the same three is one closure
 * however the domain holding them was built, and a difference in any one of them is another.
 */
class OneClosureStandsForEveryQuestionEqualToItTest {

    /** Two domains built apart over the same rules: the second is lent what the first worked
     *  out. */
    @Test
    void aDomainBuiltAgainOverTheSameRulesIsLentItsClosure() {
        ClosedStates kept = ClosedStates.kept();
        NumericDomain<String> first = holdingTwoRules(kept);
        NumericDomain<String> second = holdingTwoRules(kept);

        assertEquals(first.isBottom(), second.isBottom());
        assertEquals(first.boundsOf("b"), second.boundsOf("b"));
        assertEquals(1, kept.workedOut(),
                "two domains holding one set of rules worked their closure out apart");
    }

    /** A domain met into one that carries the closures works out through them. */
    @Test
    void whatIsMetIntoADomainIsClosedThroughTheReceiversClosures() {
        ClosedStates kept = ClosedStates.kept();
        NumericDomain<String> rules = NumericDomain.top(CanonicalOrder.asTheyAreSpelled())
                .assume(LinearForm.atomMinusConstant("a", ExactRatio.of(3)), Rel.LE,
                        Map.of("a", Granularity.DISCRETE));

        NumericDomain.top(CanonicalOrder.asTheyAreSpelled(), kept).meet(rules).boundsOf("a");
        NumericDomain.top(CanonicalOrder.asTheyAreSpelled(), kept).meet(rules).boundsOf("a");

        assertEquals(1, kept.workedOut());
    }

    @Test
    void theSameRulesSpacedAnotherWayAreAnotherQuestion() {
        ClosedStates kept = ClosedStates.kept();
        List<AffineConstraint<String>> rules = List.of(rule("a", 1, "b", -1, -2));

        kept.of(rules, atom -> Granularity.DISCRETE, CanonicalOrder.asTheyAreSpelled());
        kept.of(rules, atom -> atom.equals("a") ? Granularity.DENSE : Granularity.DISCRETE,
                CanonicalOrder.asTheyAreSpelled());

        assertEquals(2, kept.workedOut());
    }

    /** What is spaced at a position no rule weighs is nothing the closure reads. */
    @Test
    void theSpacingOfAPositionNoRuleWeighsIsNoPartOfTheQuestion() {
        ClosedStates kept = ClosedStates.kept();
        List<AffineConstraint<String>> rules = List.of(rule("a", 1, "b", -1, -2));

        kept.of(rules, atom -> Granularity.DISCRETE, CanonicalOrder.asTheyAreSpelled());
        kept.of(rules, atom -> atom.equals("c") ? Granularity.DENSE : Granularity.DISCRETE,
                CanonicalOrder.asTheyAreSpelled());

        assertEquals(1, kept.workedOut());
    }

    /** An order written again is the same order, though it is another object. */
    @Test
    void anOrderWrittenAgainIsTheSameOrder() {
        ClosedStates kept = ClosedStates.kept();
        List<AffineConstraint<String>> rules = List.of(rule("a", 1, "b", -1, -2));

        ClosedState<String> once = kept.of(rules, atom -> Granularity.DISCRETE, String::compareTo);
        ClosedState<String> again = kept.of(rules, atom -> Granularity.DISCRETE, String::compareTo);

        assertSame(once, again);
        assertEquals(1, kept.workedOut());
    }

    @Test
    void anOrderPuttingThePositionsElsewhereIsAnotherQuestion() {
        ClosedStates kept = ClosedStates.kept();
        List<AffineConstraint<String>> rules = List.of(rule("a", 1, "b", -1, -2));

        kept.of(rules, atom -> Granularity.DISCRETE, String::compareTo);
        kept.of(rules, atom -> Granularity.DISCRETE, (one, other) -> other.compareTo(one));

        assertEquals(2, kept.workedOut());
    }

    /** The rules in another order are another question: what is kept does not lean on the closure
     *  coming out the same whatever order the rules are in. */
    @Test
    void theRulesInAnotherOrderAreAnotherQuestion() {
        ClosedStates kept = ClosedStates.kept();
        AffineConstraint<String> one = rule("a", 1, "b", -1, -2);
        AffineConstraint<String> other = rule("b", 1, "c", -1, -3);

        kept.of(List.of(one, other), atom -> Granularity.DISCRETE,
                CanonicalOrder.asTheyAreSpelled());
        kept.of(List.of(other, one), atom -> Granularity.DISCRETE,
                CanonicalOrder.asTheyAreSpelled());

        assertEquals(2, kept.workedOut());
    }

    @Test
    void nothingIsKeptWhereNothingIsAskedToBe() {
        List<AffineConstraint<String>> rules = List.of(rule("a", 1, "b", -1, -2));

        ClosedState<String> once = ClosedStates.NONE.of(rules, atom -> Granularity.DISCRETE,
                CanonicalOrder.asTheyAreSpelled());
        ClosedState<String> again = ClosedStates.NONE.of(rules, atom -> Granularity.DISCRETE,
                CanonicalOrder.asTheyAreSpelled());

        assertNotSame(once, again);
        assertEquals(0, ClosedStates.NONE.workedOut());
    }

    /**
     * Two positions an order cannot tell apart, in rules that never weigh them together, are
     * closed rather than refused.
     *
     * <p>The order here ties every name of one letter. A walk of a form holding two of them would
     * refuse the pair, and none of these rules holds two; putting every position the rules weigh
     * in one walk would be a refusal none of the closure's own readings makes.
     */
    @Test
    void positionsAnOrderTiesInRulesApartAreClosedRatherThanRefused() {
        CanonicalOrder<String> byLength = (one, other) -> Integer.compare(one.length(),
                other.length());
        List<AffineConstraint<String>> rules = List.of(
                rule("a", 1, "bb", -1, -2),
                rule("c", 1, "bb", 1, -9),
                rule("bb", 1, "a", 0, 0));

        ClosedState<String> closed =
                ClosedStates.kept().of(rules, atom -> Granularity.DISCRETE, byLength);

        assertEquals(ExactCut.inclusive(ExactRatio.of(2)), closed.box().mostOf("a"),
                "bb at most nought and a at most two above it");
    }

    private static NumericDomain<String> holdingTwoRules(ClosedStates kept) {
        Map<String, Granularity> spacing = Map.of("a", Granularity.DISCRETE,
                "b", Granularity.DISCRETE);
        return NumericDomain.top(CanonicalOrder.asTheyAreSpelled(), kept)
                .assume(LinearForm.atomMinusConstant("a", ExactRatio.of(3)), Rel.GE, spacing)
                .assume(form("a", 1, "b", -1, 0), Rel.LE, spacing);
    }

    private static LinearForm<String> form(String one, long oneWeight, String other,
                                           long otherWeight, long constant) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(one, ExactRatio.of(oneWeight));
        if (otherWeight != 0) {
            coefs.put(other, ExactRatio.of(otherWeight));
        }
        return new LinearForm<>(ExactRatio.of(constant), coefs);
    }

    /** {@code one*oneWeight + other*otherWeight + constant <= 0}, read as the arithmetic reads
     *  it. */
    private static AffineConstraint<String> rule(String one, long oneWeight, String other,
                                                 long otherWeight, long constant) {
        LinearForm<String> written = form(one, oneWeight, other, otherWeight, constant);
        Read<String> read = AffineConstraint.of(written.coefs(), written.constant(), Rel.LE,
                atom -> Granularity.DISCRETE);
        assertInstanceOf(Read.Stated.class, read);
        return ((Read.Stated<String>) read).constraint();
    }
}
