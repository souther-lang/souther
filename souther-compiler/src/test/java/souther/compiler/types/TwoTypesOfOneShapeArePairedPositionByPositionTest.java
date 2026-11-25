package souther.compiler.types;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Two types taken apart at the positions they share, and one put back together from what was
 * worked out at each.
 *
 * <p>Every compound constructor, since which positions two of them line up at is what this says and
 * each has its own; two of one constructor that hold different numbers of positions, which are not
 * one shape; and two constructors that differ, and a leaf, which hold none to pair.
 */
class TwoTypesOfOneShapeArePairedPositionByPositionTest {

    private static final Type A = Type.INT;
    private static final Type B = Type.STRING;
    private static final Type C = Type.BOOL;
    private static final Type D = Type.DECIMAL;

    @Test
    void eachConstructorPairsItsPositionsInTheOrderTheyAreWalked() {
        assertEquals(List.of(new Type.Paired(A, B)), Type.paired(Type.list(A), Type.list(B)));
        assertEquals(List.of(new Type.Paired(A, B)), Type.paired(Type.set(A), Type.set(B)));
        assertEquals(List.of(new Type.Paired(A, B)), Type.paired(Type.option(A), Type.option(B)));
        assertEquals(List.of(new Type.Paired(A, C), new Type.Paired(B, D)),
                Type.paired(Type.map(A, B), Type.map(C, D)));
        assertEquals(List.of(new Type.Paired(A, C), new Type.Paired(B, D)),
                Type.paired(Type.tuple(List.of(A, B)), Type.tuple(List.of(C, D))));
        assertEquals(List.of(new Type.Paired(A, C), new Type.Paired(B, D)),
                Type.paired(Type.fn(List.of(A), B), Type.fn(List.of(C), D)));
    }

    @Test
    void twoOfOneConstructorHoldingDifferentlyManyAreNotPaired() {
        assertNull(Type.paired(Type.tuple(List.of(A, B)), Type.tuple(List.of(A, B, C))));
        assertNull(Type.paired(Type.fn(List.of(A), B), Type.fn(List.of(A, C), B)));
    }

    @Test
    void twoConstructorsOrALeafAreNotPaired() {
        assertNull(Type.paired(Type.list(A), Type.set(A)));
        assertNull(Type.paired(A, A));
        assertNull(Type.paired(Type.list(A), A));
        assertNull(Type.paired(A, Type.list(A)));
    }

    @Test
    void whatWasWorkedOutAtEachPositionIsPutBack() {
        assertEquals(Type.map(C, D), Type.withChildren(Type.map(A, B), List.of(C, D)));
        assertEquals(Type.fn(List.of(C, D), A),
                Type.withChildren(Type.fn(List.of(A, B), C), List.of(C, D, A)));
        assertEquals(A, Type.withChildren(A, List.of()));
        assertThrows(IllegalArgumentException.class,
                () -> Type.withChildren(Type.list(A), List.of(B, C)));
        assertThrows(IllegalArgumentException.class, () -> Type.withChildren(A, List.of(B)));
    }
}
