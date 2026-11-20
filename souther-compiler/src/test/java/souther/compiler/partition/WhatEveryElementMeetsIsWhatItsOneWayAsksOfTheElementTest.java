package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What every element of a container meets, whichever element it is
 * ({@link RowDemand.ForAll#heldOfEveryElement}), is what the one way the reading states asks of the
 * element itself. What some element of a container inside the element is asked holds of that
 * element alone: {@code [[0, MAX]]} meets "every list holds some element below MAX", and its
 * greatest element is MAX.
 */
class WhatEveryElementMeetsIsWhatItsOneWayAsksOfTheElementTest {

    private static final TermPath LISTS = TermPath.of("dss");

    private static final TermPath A_LIST = LISTS.element();

    @Test
    void whatTheOneWayAsksOfTheElementIsMetByEveryElement() {
        RowDemand.Relational belowMax = below(A_LIST);
        assertEquals(List.of(belowMax), every(List.of(List.of(belowMax))).heldOfEveryElement());
    }

    /** The relation is one a row written alike is composed to meet, and no element of the inner
     *  list other than the one that meets it is held to it. */
    @Test
    void whatSomeElementOfAListInsideTheElementIsAskedIsMetByThatOneAlone() {
        RowDemand.Relational belowMax = below(A_LIST.element());
        RowDemand.ForAll every = every(List.of(List.of(
                new RowDemand.SomeElementWithin(A_LIST, List.of(belowMax)))));
        assertEquals(List.of(belowMax), every.relations());
        assertTrue(every.heldOfEveryElement().isEmpty());
    }

    @Test
    void anElementMeetingOneOfTwoWaysMeetsNeitherForSure() {
        RowDemand.ForAll every = every(List.of(List.of(below(A_LIST)),
                List.of(new RowDemand.Relational(new TakenConstraint.Affine(
                        LinearForm.atom(new NumericTerm.ValueOf(A_LIST)), Rel.GE)))));
        assertTrue(every.heldOfEveryElement().isEmpty());
    }

    /** That {@code at} lies below the greatest {@code Int}. */
    private static RowDemand.Relational below(TermPath at) {
        return new RowDemand.Relational(new TakenConstraint.Affine(new LinearForm<>(
                ExactRatio.of(-Long.MAX_VALUE), Map.of(new NumericTerm.ValueOf(at), ExactRatio.ONE)),
                Rel.LT));
    }

    private static RowDemand.ForAll every(
            List<? extends List<? extends RowDemand.AskedOfAnElement>> ways) {
        return new RowDemand.ForAll(LISTS, new RowDemand.AnElementMeets(ways),
                below(LISTS), Optional.empty());
    }
}
