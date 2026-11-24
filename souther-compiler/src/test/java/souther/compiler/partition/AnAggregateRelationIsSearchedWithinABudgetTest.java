package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.function.IntPredicate;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Looking for the counts that hold a relation among counts of one container's elements is bounded
 * by a figure, and what a search that reached a figure comes back with says which.
 *
 * <p>A relation can be one no whole number meets while every part of it, taken as a range, still
 * may: the sum of even weights is never odd, and the ends of the ranges leave it open. Such a
 * search is walked to the end of what it is allowed, and nothing is shown impossible by it.
 */
class AnAggregateRelationIsSearchedWithinABudgetTest {

    private static final int MOST = CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();

    private static final TermPath XS = TermPath.of("xs");

    /** A count of the elements of {@code xs} above {@code above}. */
    private static Quantity.HowManyMeet above(int above) {
        NumericTerm element = new NumericTerm.ValueOf(XS.element());
        Proposition meets = new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-above),
                Map.of(new DecisionAtom.OfTheInput(element), ExactRatio.ONE)), Rel.GT), true);
        return new Quantity.HowManyMeet(new DecisionSubject.AnInput(XS), meets);
    }

    private static AggregateRelation weighing(int[] weights, int constant, Rel rel) {
        SequencedMap<Quantity.HowManyMeet, ExactRatio> counts = new LinkedHashMap<>();
        for (int i = 0; i < weights.length; i++) {
            counts.put(above(i), ExactRatio.of(weights[i]));
        }
        return new AggregateRelation(XS, counts, ExactRatio.ZERO, ExactRatio.of(constant), rel);
    }

    private static List<IntPredicate> anyNumber(int counts) {
        return Collections.nCopies(counts, n -> true);
    }

    @Test
    void theFewestCountsThatHoldARelationAreFound() {
        AggregateRelation either = weighing(new int[] {1, 1}, -1, Rel.EQ);
        AggregateRelation.Fewest found = either.fewestWithin(MOST, anyNumber(2));
        assertArrayEquals(new int[] {0, 1},
                assertInstanceOf(AggregateRelation.Fewest.Found.class, found).meeting());
    }

    /** No container of the most elements has them: it is that figure, which is no impossibility. */
    @Test
    void whereNoContainerOfTheMostElementsHoldsItTheFigureIsTheMostElements() {
        AggregateRelation farMore = weighing(new int[] {1, -1}, -(MOST + 5), Rel.GE);
        assertEquals(new AggregateRelation.Fewest.Missing(
                        CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH),
                farMore.fewestWithin(MOST, anyNumber(2)));
    }

    /**
     * Seven counts weighed evenly against an odd number: every range still leaves the sum open, so
     * the search is walked until it is stopped, and says the figure that stopped it.
     */
    @Test
    void aRelationNoWholeNumberMeetsStopsAtAFigureAndSaysSo() {
        AggregateRelation odd = weighing(new int[] {2, -2, 2, -2, 2, -2, 2}, -1, Rel.EQ);
        assertEquals(new AggregateRelation.Fewest.Missing(
                        CompositionBudget.TUPLES_OF_COUNTS_A_RELATION_IS_TRIED_AT),
                odd.fewestWithin(MOST, anyNumber(7)));
    }
}
