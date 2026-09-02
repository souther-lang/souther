package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What a rule cuts, told from how much of it the rule happened to write.
 *
 * <p>{@code n > 10} and {@code 2 * n > 40} cut the same thing in the same place: the second says it
 * in twos, and the values of {@code n} part between twenty and twenty-one either way. Held apart,
 * the first divides the position into classes and the second draws a line on an arithmetic form that
 * divides no position at all — so the report counts two equivalence partitions where the model
 * states three, and neither rule's border knows the other is there.
 *
 * <p>What makes them one is the direction and not the size: a form and any positive multiple of it
 * order the rows the same way, and how far along the line falls is the cut's to say rather than the
 * quantity's. The same argument that moved the constant out of a quantity, taken one step further.
 */
class TwoSpellingsOfOneDirectionAreOneQuantityTest {

    private static NumericTerm term(String name) {
        return new NumericTerm.ValueOf(TermPath.of(name));
    }

    /** The form {@code c1 * t1 + c2 * t2 ...}, written as the pairs an author would read. */
    private static LinearForm<NumericTerm> form(Object... pairs) {
        Map<NumericTerm, BigDecimal> coefs = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            coefs.put(term((String) pairs[i]), new BigDecimal((String) pairs[i + 1]));
        }
        return new LinearForm<>(BigDecimal.ZERO, coefs);
    }

    /**
     * A position and a multiple of it are one quantity.
     *
     * <p>Which is what puts {@code 2 * n > 40} back on the position it divides. Read as a form over
     * {@code 2 * n}, it contributes no class to {@code n} at all, and a report says the model draws
     * one line through the position where it draws two.
     */
    @Test
    void aPositionAndAMultipleOfItAreOneQuantity() {
        assertEquals(QuantityKey.of(form("n", "1")).key(), QuantityKey.of(form("n", "2")).key());
    }

    /** And a form and a multiple of it, which is the same argument with more than one position. */
    @Test
    void aFormAndAMultipleOfItAreOneQuantity() {
        assertEquals(QuantityKey.of(form("a", "1", "b", "2")).key(),
                QuantityKey.of(form("a", "3", "b", "6")).key());
    }

    /**
     * Two directions are two quantities, however alike the coefficients look.
     *
     * <p>{@code a + b} and {@code a + 2 * b} order the rows differently, so a row inside one is not
     * inside the other. Made one, the runs of two unrelated arrangements would be merged and every
     * point of both would ask for a row in the wrong place.
     */
    @Test
    void twoDirectionsAreTwoQuantities() {
        assertNotEquals(QuantityKey.of(form("a", "1", "b", "1")).key(),
                QuantityKey.of(form("a", "1", "b", "2")).key());
    }

    /**
     * How much of the quantity a rule wrote, which is what a level written in its terms divides by.
     *
     * <p>Carried rather than worked out again where a cut is turned into the canonical quantity's
     * own units. {@code 2 * n <= 9} parts the whole numbers between four and five, and finding that
     * takes knowing the level nine was written in twos.
     */
    @Test
    void aQuantitySaysHowMuchOfItAFormWrote() {
        assertEquals(new BigDecimal("2"), QuantityKey.per(form("n", "2")));
        assertEquals(new BigDecimal("3"), QuantityKey.per(form("a", "3", "b", "6")));
        assertEquals(new BigDecimal("1"), QuantityKey.per(form("a", "1", "b", "2")));
    }
}
