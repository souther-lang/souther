package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.partition.QuantityKey;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where the rows leave a line beside a value singled out is folded so that a line with a place
 * holds one answer about the other side, and not where each of its rows stood.
 *
 * <p>A row of the other side matters only by standing at the place or not. So taking the rows in
 * together, or one at a time in any order, comes to the same line; and once a row of the naming
 * side has put the place somewhere, nothing of where the other side stood is kept — which is what
 * keeps one more row, offered or stepped to, constant work however many rows the line was left by.
 */
class ALineLeftAtOneValueHoldsNothingOfTheOtherSideOnceItsPlaceIsKnownTest {

    private static final QuantityKey DIRECTION = direction();

    private static QuantityKey direction() {
        Map<NumericTerm, ExactRatio> weights = new LinkedHashMap<>();
        weights.put(new NumericTerm.ValueOf(TermPath.of("x")), ExactRatio.of(2));
        weights.put(new NumericTerm.ValueOf(TermPath.of("y")), ExactRatio.of(-1));
        return new QuantityKey(weights);
    }

    private static AnotherLineTheRowsAllow.Stands.Read row(boolean modelKeeps, long at) {
        return new AnotherLineTheRowsAllow.Stands.Read(modelKeeps, ExactRatio.of(at));
    }

    /** Taken in together and one at a time, the other side first or after, the same line. */
    @Test
    void theRowsComeToTheSameLineHoweverTheyAreTakenIn() {
        List<List<AnotherLineTheRowsAllow.Stands.Read>> orders = List.of(
                List.of(row(false, 3), row(false, 7), row(true, 5), row(true, 5), row(false, 1)),
                List.of(row(true, 5), row(false, 3), row(true, 5), row(false, 7), row(false, 1)),
                List.of(row(false, 5), row(true, 5)),
                List.of(row(true, 5), row(false, 5)),
                List.of(row(true, 5), row(true, 6)));
        for (boolean keepsTheValue : new boolean[] {true, false}) {
            for (List<AnotherLineTheRowsAllow.Stands.Read> rows : orders) {
                AnotherLineTheRowsAllow.Stands.AtOneValue together =
                        AnotherLineTheRowsAllow.Stands.AtOneValue.none(DIRECTION, keepsTheValue)
                                .withAll(rows);
                AnotherLineTheRowsAllow.Stands.Fold oneAtATime =
                        AnotherLineTheRowsAllow.Stands.AtOneValue.none(DIRECTION, keepsTheValue);
                List<AnotherLineTheRowsAllow.Stands.Read> reversed = new ArrayList<>(rows);
                Collections.reverse(reversed);
                AnotherLineTheRowsAllow.Stands.Fold backwards =
                        AnotherLineTheRowsAllow.Stands.AtOneValue.none(DIRECTION, keepsTheValue);
                for (int at = 0; at < rows.size(); at++) {
                    oneAtATime = oneAtATime.withAt(rows.get(at).modelKeeps(), rows.get(at).at());
                    backwards = backwards.withAt(reversed.get(at).modelKeeps(),
                            reversed.get(at).at());
                }
                assertEquals(answer(together), answer(oneAtATime), rows::toString);
                assertEquals(answer(together), answer(backwards), rows::toString);
            }
        }
    }

    /** What a fold answers: whether the line still stands, and where where it does. Which place a
     *  line ruled out was first seen at is no answer about it. */
    private static String answer(AnotherLineTheRowsAllow.Stands.Fold fold) {
        return fold.apart() ? "stands at " + fold.at() : "ruled out";
    }

    /** The control: what the line comes to is what the rule says of the pair. */
    @Test
    void aSecondPlaceOrARowOfTheOtherSideAtThePlaceRulesItOut() {
        AnotherLineTheRowsAllow.Stands.AtOneValue none =
                AnotherLineTheRowsAllow.Stands.AtOneValue.none(DIRECTION, true);
        assertTrue(none.withAll(List.of(row(true, 5), row(false, 3))).apart());
        assertFalse(none.withAll(List.of(row(true, 5), row(true, 6))).apart());
        assertFalse(none.withAll(List.of(row(false, 5), row(true, 5))).apart());
    }

    /** Once a row of the naming side has put the place somewhere, where the other side stood is
     *  folded into one answer and not held, however many rows of it came first. */
    @Test
    void nothingOfWhereTheOtherSideStoodIsHeldOnceThePlaceIsKnown() {
        List<AnotherLineTheRowsAllow.Stands.Read> rows = new ArrayList<>();
        for (int at = 0; at < 50; at++) {
            rows.add(row(false, 100 + at));
        }
        AnotherLineTheRowsAllow.Stands.AtOneValue before =
                AnotherLineTheRowsAllow.Stands.AtOneValue.none(DIRECTION, true).withAll(rows);
        assertEquals(50, before.before().size(), "held while no place is known");

        AnotherLineTheRowsAllow.Stands.AtOneValue after = before.withAt(true, ExactRatio.of(5));
        assertTrue(after.before().isEmpty(), after::toString);
        assertTrue(after.apart());
        assertTrue(after.withAt(false, ExactRatio.of(7)).before().isEmpty());
    }
}
