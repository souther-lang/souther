package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Of a statement that is one of several, what is certain is what every way of it makes certain, of
 * the same number, at the weakest.
 *
 * <p>One of the ways holds and which is not said, so a bound the ways put differently is the one
 * that allows the most, and a number some way says nothing of is bounded by none.
 */
class WhatEveryWayOfAChoiceMakesCertainIsTheWeakestOfWhatEachSaysTest {

    private static final Term.Interner NAMES = new Term.Interner();
    private static final FactSubject LENGTH = FactSubject.of(NAMES.written("length"));
    private static final FactSubject OTHER = FactSubject.of(NAMES.written("other"));

    /** {@code number >= at}. */
    private static NumericConstraint atLeast(FactSubject number, long at) {
        return new NumericConstraint(
                LinearForm.atomMinusConstant(number, ExactRatio.of(at)), Rel.GE);
    }

    /** {@code number <= at}. */
    private static NumericConstraint atMost(FactSubject number, long at) {
        return new NumericConstraint(
                LinearForm.atomMinusConstant(number, ExactRatio.of(at)), Rel.LE);
    }

    @Test
    void theWeakestLowerBoundAndTheWeakestUpperBoundAreWhatIsCertain() {
        assertEquals(List.of(atLeast(LENGTH, 3), atMost(LENGTH, 5)), NumericConstraint.commonTo(
                List.of(List.of(atLeast(LENGTH, 3), atMost(LENGTH, 3)),
                        List.of(atLeast(LENGTH, 5), atMost(LENGTH, 5)))));
    }

    @Test
    void aBoundOnlySomeWaysPutIsNoBound() {
        assertEquals(List.of(atLeast(LENGTH, 3)), NumericConstraint.commonTo(
                List.of(List.of(atLeast(LENGTH, 3), atMost(LENGTH, 4)),
                        List.of(atLeast(LENGTH, 5)))), "the ceiling is only one way's");
    }

    @Test
    void aWayThatSaysNothingLeavesNothingCertain() {
        assertEquals(List.of(), NumericConstraint.commonTo(
                List.of(List.of(atLeast(LENGTH, 3)), List.of())));
    }

    @Test
    void aBoundOfOneNumberIsNotABoundOfAnother() {
        assertEquals(List.of(), NumericConstraint.commonTo(
                List.of(List.of(atLeast(LENGTH, 3)), List.of(atLeast(OTHER, 3)))));
    }

    @Test
    void theStrongestOfTheBoundsOneWayPutsIsWhatThatWaySays() {
        assertEquals(List.of(atLeast(LENGTH, 4)), NumericConstraint.commonTo(
                List.of(List.of(atLeast(LENGTH, 2), atLeast(LENGTH, 6)),
                        List.of(atLeast(LENGTH, 4)))));
    }

    @Test
    void anEqualityIsABoundEitherWay() {
        NumericConstraint three = new NumericConstraint(
                LinearForm.atomMinusConstant(LENGTH, ExactRatio.of(3)), Rel.EQ);
        assertEquals(List.of(atLeast(LENGTH, 3), atMost(LENGTH, 5)), NumericConstraint.commonTo(
                List.of(List.of(three), List.of(atLeast(LENGTH, 5), atMost(LENGTH, 5)))));
    }
}
