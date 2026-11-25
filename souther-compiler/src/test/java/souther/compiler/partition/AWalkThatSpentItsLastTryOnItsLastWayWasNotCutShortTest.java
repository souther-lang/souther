package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;

import java.util.ArrayList;
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
 * the walk wherever it is. The three are what a search reporting "nothing within what is tried"
 * stands on, and only the second is that.
 */
class AWalkThatSpentItsLastTryOnItsLastWayWasNotCutShortTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final NumericTerm Y = new NumericTerm.ValueOf(TermPath.of("y"));
    private static final List<ExactRatio> THREE =
            List.of(ExactRatio.of(0), ExactRatio.of(1), ExactRatio.of(2));

    private static Map<NumericTerm, List<ExactRatio>> tried() {
        Map<NumericTerm, List<ExactRatio>> tried = new LinkedHashMap<>();
        tried.put(X, THREE);
        tried.put(Y, THREE);
        return tried;
    }

    @Test
    void aFigureAsLargeAsTheWaysAsksEachAndLeavesNothing() {
        StopAssessment.Tries left = new StopAssessment.Tries(9);
        List<Map<NumericTerm, ExactRatio>> asked = new ArrayList<>();
        assertNull(TriedInTurn.first(List.of(X, Y), tried(), left, values -> {
            asked.add(Map.copyOf(values));
            return null;
        }));
        assertEquals(9, asked.size());
        assertFalse(left.cutShort(), "every way was asked");
    }

    @Test
    void aFigureShortOfTheWaysSaysItLeftSome() {
        StopAssessment.Tries left = new StopAssessment.Tries(8);
        int[] asked = {0};
        assertNull(TriedInTurn.first(List.of(X, Y), tried(), left, values -> {
            asked[0]++;
            return null;
        }));
        assertEquals(8, asked[0]);
        assertTrue(left.cutShort(), "the ninth way was left");
    }

    @Test
    void aWayThatAnswersIsTheAnswer() {
        StopAssessment.Tries left = new StopAssessment.Tries(9);
        Map<NumericTerm, ExactRatio> found = TriedInTurn.first(List.of(X, Y), tried(), left,
                values -> values.get(X).equals(ExactRatio.of(1)) && values.get(Y).equals(
                        ExactRatio.of(2)) ? Map.copyOf(values) : null);
        assertEquals(Map.of(X, ExactRatio.of(1), Y, ExactRatio.of(2)), found);
        assertFalse(left.cutShort());
    }
}
