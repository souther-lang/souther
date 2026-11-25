package souther.compiler.types;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two types taken apart at the positions they share, and the first put back together from what
 * was worked out at each.
 *
 * <p>Every compound constructor, since which positions two of them line up at is what this says and
 * each has its own; two of one constructor that hold different numbers of positions, which are not
 * one shape; two constructors that differ, and a leaf, which hold none to pair; and a walk that
 * changes nothing, which hands back the type it was given.
 */
class TwoTypesOfOneShapeArePairedPositionByPositionTest {

    private static final Type A = Type.INT;
    private static final Type B = Type.STRING;
    private static final Type C = Type.BOOL;
    private static final Type D = Type.DECIMAL;

    private static List<List<Type>> pairs(Type one, Type other) {
        List<List<Type>> out = new ArrayList<>();
        assertTrue(Type.everyPaired(one, other, (a, b) -> out.add(List.of(a, b))));
        return out;
    }

    @Test
    void eachConstructorPairsItsPositionsInTheOrderTheyAreWalked() {
        assertEquals(List.of(List.of(A, B)), pairs(Type.list(A), Type.list(B)));
        assertEquals(List.of(List.of(A, B)), pairs(Type.set(A), Type.set(B)));
        assertEquals(List.of(List.of(A, B)), pairs(Type.option(A), Type.option(B)));
        assertEquals(List.of(List.of(A, C), List.of(B, D)), pairs(Type.map(A, B), Type.map(C, D)));
        assertEquals(List.of(List.of(A, C), List.of(B, D)),
                pairs(Type.tuple(List.of(A, B)), Type.tuple(List.of(C, D))));
        assertEquals(List.of(List.of(A, C), List.of(B, D)),
                pairs(Type.fn(List.of(A), B), Type.fn(List.of(C), D)));
    }

    @Test
    void twoNotOfOneShapeAreNotPaired() {
        assertFalse(Type.ofOneShape(Type.tuple(List.of(A, B)), Type.tuple(List.of(A, B, C))));
        assertFalse(Type.ofOneShape(Type.fn(List.of(A), B), Type.fn(List.of(A, C), B)));
        assertFalse(Type.ofOneShape(Type.list(A), Type.set(A)));
        assertFalse(Type.ofOneShape(A, A));
        assertFalse(Type.ofOneShape(Type.list(A), A));
        assertFalse(Type.ofOneShape(A, Type.list(A)));
        assertFalse(Type.everyPaired(Type.list(A), Type.set(A), (a, b) -> true));
        assertNull(Type.zipped(Type.list(A), A, (a, b) -> a));
    }

    @Test
    void aWalkEndsWhereAPositionAnswersNothing() {
        int[] asked = {0};
        assertFalse(Type.everyPaired(Type.map(A, B), Type.map(C, D), (a, b) -> ++asked[0] > 1));
        assertEquals(1, asked[0]);
        assertNull(Type.zipped(Type.map(A, B), Type.map(C, D), (a, b) -> null));
    }

    @Test
    void whatWasWorkedOutAtEachPositionIsPutBackAndNothingIsMadeWhereNothingChanged() {
        assertEquals(Type.map(C, D), Type.zipped(Type.map(A, B), Type.map(C, D), (a, b) -> b));
        assertEquals(Type.fn(List.of(C), D),
                Type.zipped(Type.fn(List.of(A), B), Type.fn(List.of(C), D), (a, b) -> b));
        Type same = Type.tuple(List.of(A, B));
        assertSame(same, Type.zipped(same, Type.tuple(List.of(C, D)), (a, b) -> a));
    }
}
