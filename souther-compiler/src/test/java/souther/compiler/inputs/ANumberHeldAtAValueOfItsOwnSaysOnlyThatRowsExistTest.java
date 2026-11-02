package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Over a type that holds {@code -5} to {@code 4}, the operations of {@code x + c + 4 - 4 >= c + y}
 * are {@code x + c + 4}, {@code x + c} and {@code c + y}, and the number {@code c} the comparison
 * cancels is held at nought.
 *
 * <p>A row of {@code x} and {@code y} computed with {@code c} at nought is a row. A value of
 * {@code x} with none there is not a value with none: {@code x} of 2 stops at {@code x + c + 4}
 * with {@code c} at nought and gets past every operation with {@code c} at -2, for {@code y} of
 * 1 and of 3. So what is told at held values is that rows exist, and is no reading of the rows
 * computed that says where there are none ({@link RowsOfTheTwo}).
 */
class ANumberHeldAtAValueOfItsOwnSaysOnlyThatRowsExistTest {

    private static final int LEAST = -5;
    private static final int GREATEST = 4;

    private static IntSum sum(int onX, int onC, int onY, int constant) {
        Map<Object, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put("x", ExactRatio.of(onX));
        coefs.put("c", ExactRatio.of(onC));
        coefs.put("y", ExactRatio.of(onY));
        return new IntSum(coefs, ExactRatio.of(constant), BigInteger.valueOf(LEAST),
                BigInteger.valueOf(GREATEST));
    }

    private static final List<IntSum> SUMS = List.of(sum(1, 1, 0, 4), sum(1, 1, 0, 0),
            sum(0, 1, 1, 0));

    private static Operations heldAtNought() {
        return new Operations(SUMS, List.of(), Told.EVERY_AT_HELD_VALUES,
                Map.of("c", ExactRatio.ZERO));
    }

    private static boolean getsPast(int x, int c, int y) {
        for (IntSum each : SUMS) {
            int at = (int) (each.coefs().get("x").floor().orNull().longValue() * x
                    + each.coefs().get("c").floor().orNull().longValue() * c
                    + each.coefs().get("y").floor().orNull().longValue() * y
                    + each.constant().floor().orNull().longValue());
            if (at < LEAST || at > GREATEST) {
                return false;
            }
        }
        return true;
    }

    private static boolean someRowGetsPast(int x, int y) {
        for (int c = LEAST; c <= GREATEST; c++) {
            if (getsPast(x, c, y)) {
                return true;
            }
        }
        return false;
    }

    @Test
    void aRowComputedAtTheHeldValueIsARowOfTheType() {
        RowsComputed rows = RowsComputed.ENDLESS.withOperations(heldAtNought());
        int shown = 0;
        for (int x = LEAST; x <= GREATEST; x++) {
            for (int y = LEAST; y <= GREATEST; y++) {
                int at = x;
                int and = y;
                boolean computed = rows.computedAt(() -> Map.of("x", ExactRatio.of(at),
                        "y", ExactRatio.of(and)));
                assertEquals(getsPast(x, 0, y), computed, "x " + x + ", y " + y);
                if (computed) {
                    shown++;
                    assertTrue(someRowGetsPast(x, y), "x " + x + ", y " + y);
                }
            }
        }
        assertTrue(shown > 0, "no row was ever shown computed");
    }

    @Test
    void aValueWithNoRowAtTheHeldValueMayHaveOneAtAnother() {
        RowsComputed rows = RowsComputed.ENDLESS.withOperations(heldAtNought());
        for (int y : List.of(1, 3)) {
            int partner = y;
            assertFalse(rows.computedAt(() -> Map.of("x", ExactRatio.of(2),
                    "y", ExactRatio.of(partner))), "y " + y);
            assertTrue(getsPast(2, -2, y), "y " + y);
        }
    }

    @Test
    void theRowsAtAHeldValueAreNotReadAsAllTheRowsComputed() {
        Operations held = heldAtNought();

        assertTrue(held.exactAtTheHeldValues());
        assertFalse(held.exact());
        assertNull(RowsOfTheTwo.of(held, "x", "y", Map.of()));
        assertTrue(held.canStopARow());
        assertFalse(held.theSizesAreRowsComputed(List.of(), ExactRatio.ZERO));
    }

    @Test
    void numbersAreHeldAtValuesExactlyWhereTheOperationsAreToldAtThem() {
        assertThrows(IllegalArgumentException.class,
                () -> new Operations(SUMS, List.of(), Told.EVERY_AT_HELD_VALUES, Map.of()));
        assertThrows(IllegalArgumentException.class,
                () -> new Operations(SUMS, List.of(), Told.EVERY, Map.of("c", ExactRatio.ZERO)));
        assertThrows(IllegalArgumentException.class,
                () -> new Operations(SUMS, List.of(), Told.SOME, Map.of("c", ExactRatio.ZERO)));
    }
}
