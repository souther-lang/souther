package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A test of the position says whether it holds of every position a list has, or of none, and a
 * choice made by such a test is the one answer every element takes.
 *
 * <p>Asked of every relation, a range of values to compare against, the position itself and the
 * remainders a few divisors leave, either sign — and held to what the test says of each position
 * one at a time. The positions run past where any of these values or remainders lies, so what the
 * positions further on come to is what the last of them came to.
 */
class ATestOfThePositionThatHoldsEverywhereOrNowhereChoosesNothingTest {

    private static final int POSITIONS = 24;

    @Test
    void everyAndNoneAreWhatTheTestSaysOfEachPosition() {
        List<String> wrong = new ArrayList<>();
        for (long divisor : new long[] {ElementValue.PositionTest.THE_POSITION_ITSELF, 1, 2, 3, -2,
                -3}) {
            for (Rel relation : Rel.values()) {
                for (long against = -4; against <= 4; against++) {
                    ElementValue.PositionTest test =
                            new ElementValue.PositionTest(divisor, relation, against);
                    boolean every = true;
                    boolean none = true;
                    for (int position = 0; position < POSITIONS; position++) {
                        every &= test.holdsOf(position);
                        none &= !test.holdsOf(position);
                    }
                    if (every != test.holdsOfEveryPosition() || none != test.holdsOfNoPosition()) {
                        wrong.add(test + ": every " + every + ", none " + none);
                    }
                }
            }
        }
        assertEquals(List.of(), wrong, "what a test says of every position is what it says of each");
    }

    /** The denial holds exactly where the test does not. */
    @Test
    void theDenialHoldsWhereTheTestDoesNot() {
        ElementValue.PositionTest test = new ElementValue.PositionTest(3, Rel.LE, 1);
        for (int position = 0; position < POSITIONS; position++) {
            assertEquals(!test.holdsOf(position), test.denied().holdsOf(position));
        }
    }

    /** From nought on is every position, and before nought is none: the choice is no choice. */
    @Test
    void aChoiceByATestThatHoldsEverywhereOrNowhereIsTheAnswerTaken() {
        ElementValue itself = new ElementValue.Affine(LinearForm.atom(
                ElementProjection.ofFields(List.of())));
        ElementValue nought = new ElementValue.Affine(new LinearForm<>(ExactRatio.ZERO, Map.of()));
        ElementValue.PositionTest fromNought = new ElementValue.PositionTest(
                ElementValue.PositionTest.THE_POSITION_ITSELF, Rel.GE, 0);
        assertEquals(itself, ElementValue.choosingByPosition(fromNought, itself, nought));
        assertEquals(nought, ElementValue.choosingByPosition(fromNought.denied(), itself, nought));
        assertInstanceOf(ElementValue.ByPosition.class, ElementValue.choosingByPosition(
                new ElementValue.PositionTest(ElementValue.PositionTest.THE_POSITION_ITSELF,
                        Rel.LT, 2), itself, nought));
    }
}
