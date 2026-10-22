package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One of each of several parts, taken together, where the combinations are more than are looked
 * along: each of each part once, beside the first of the others, and no part passed over for
 * another's ({@link OneOfEach#ofEachPart}).
 *
 * <p>A way past a guard of two parts, the first with a few ways of holding it and the second with
 * many: cut to its first combinations, every choice would hold the first part to its first way,
 * and a row past the guard only along its second would never be looked for.
 */
class WaysTakenOneOfEachPartPassNoPartOverTest {

    @Test
    void everyCombinationWhereTheyAreNoMoreThanTheFigure() {
        OneOfEach.Taken<String> taken =
                OneOfEach.ofEachPart(List.of(List.of("a1", "a2"), List.of("b1", "b2")), 4);
        assertTrue(taken.everyWay());
        assertEquals(List.of(List.of("a1", "b1"), List.of("a1", "b2"), List.of("a2", "b1"),
                List.of("a2", "b2")), taken.ways());
    }

    @Test
    void pastTheFigureEachWayOfEachPartIsTakenBeforeAnyPartsThird() {
        OneOfEach.Taken<String> taken = OneOfEach.ofEachPart(List.of(
                List.of("a1", "a2", "a3"),
                List.of("b1", "b2", "b3", "b4", "b5", "b6")), 4);
        assertFalse(taken.everyWay());
        assertEquals(List.of(List.of("a1", "b1"), List.of("a2", "b1"), List.of("a1", "b2"),
                List.of("a3", "b1")), taken.ways());
    }
}
