package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;

import java.util.AbstractList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The ways of putting two numbers at the values tried for each, asked while a figure lasts.
 *
 * <p>Two numbers tried at three values each are nine ways. A figure of nine asks all of them and
 * leaves nothing; a figure of eight leaves the last one, and that is said; a way that answers ends
 * the walk wherever it is. A number with no value to be tried at leaves no way at all: nothing is
 * asked or spent, nothing is left, and the values of the numbers ahead of it are not walked — at
 * any figure, nought included.
 */
class AWalkThatSpentItsLastTryOnItsLastWayWasNotCutShortTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final NumericTerm Y = new NumericTerm.ValueOf(TermPath.of("y"));
    private static final List<ExactRatio> THREE =
            List.of(ExactRatio.of(0), ExactRatio.of(1), ExactRatio.of(2));

    private static Map<NumericTerm, List<ExactRatio>> tried(List<ExactRatio> ofX,
                                                            List<ExactRatio> ofY) {
        Map<NumericTerm, List<ExactRatio>> tried = new LinkedHashMap<>();
        tried.put(X, ofX);
        tried.put(Y, ofY);
        return tried;
    }

    private static int asked(Tries left, Map<NumericTerm, List<ExactRatio>> tried) {
        int[] asked = {0};
        assertNull(TriedInTurn.first(List.of(X, Y), tried, left, values -> {
            asked[0]++;
            return null;
        }));
        return asked[0];
    }

    @Test
    void aFigureAsLargeAsTheWaysAsksEachAndLeavesNothing() {
        Tries left = new Tries(9);
        assertEquals(9, asked(left, tried(THREE, THREE)));
        assertFalse(left.cutShort(), "every way was asked");
    }

    @Test
    void aFigureShortOfTheWaysSaysItLeftSome() {
        Tries left = new Tries(8);
        assertEquals(8, asked(left, tried(THREE, THREE)));
        assertTrue(left.cutShort(), "the ninth way was left");
    }

    @Test
    void aWayThatAnswersIsTheAnswer() {
        Tries left = new Tries(9);
        Map<NumericTerm, ExactRatio> found = TriedInTurn.first(List.of(X, Y), tried(THREE, THREE),
                left, values -> values.get(X).equals(ExactRatio.of(1)) && values.get(Y).equals(
                        ExactRatio.of(2)) ? Map.copyOf(values) : null);
        assertEquals(Map.of(X, ExactRatio.of(1), Y, ExactRatio.of(2)), found);
        assertFalse(left.cutShort());
    }

    @Test
    void aNumberWithNoValueToBeTriedAtLeavesNoWayAndNothingUndone() {
        for (int figure : new int[] {0, 9}) {
            Tries left = new Tries(figure);
            assertEquals(0, asked(left, tried(THREE, List.of())));
            assertFalse(left.cutShort(), "no way was left at a figure of " + figure);
            assertEquals(figure == 0, left.spent(), "nothing was spent");
        }
    }

    /**
     * Thirty lists of two are more than a thousand million ways, and a walk held to three makes
     * three of them: each way is made as it is asked for, so what is read of the lists is what
     * three ways hold and the figure ends the making.
     */
    @Test
    void aWalkHeldToAFigureMakesNoMoreWaysThanItSpendsOn() {
        int[] read = {0};
        List<Integer> two = new AbstractList<>() {
            @Override
            public Integer get(int index) {
                read[0]++;
                return index;
            }

            @Override
            public int size() {
                return 2;
            }
        };
        List<List<Integer>> lists = Collections.nCopies(30, two);
        Tries three = new Tries(3);
        int[] handed = {0};
        assertEquals(DepthFirst.Walked.CUT_SHORT, EveryWayOfChoosing.each(lists, three, way -> {
            handed[0]++;
            return true;
        }));
        assertEquals(3, handed[0], "three ways handed out");
        assertEquals(3 * 30, read[0], "and no more of the lists read than three ways hold");
    }

    @Test
    void theListsAheadOfAnEmptyOneAreNotWalked() {
        int[] read = {0};
        List<Integer> ahead = new AbstractList<>() {
            @Override
            public Integer get(int index) {
                read[0]++;
                return index;
            }

            @Override
            public int size() {
                return 1000;
            }
        };
        Tries tries = new Tries(1);
        assertEquals(DepthFirst.Walked.EVERY_END_REACHED,
                EveryWayOfChoosing.each(List.of(ahead, ahead, List.<Integer>of()), tries,
                        chosen -> {
                            throw new AssertionError("there is no way to hand out: " + chosen);
                        }));
        assertEquals(0, read[0], "the values ahead of the empty list were read");
        assertFalse(tries.spent(), "nothing was spent");
    }
}
