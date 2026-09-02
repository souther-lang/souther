package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A pair of orders held beside a number is held beside the number it is of.
 *
 * <p>Some readers cannot drop the number: a class of a count and a coordinate of a border are about
 * a position's own number, which is the narrower kind of term, and the orders say which number they
 * are of without saying that. Two components are two things to get right, and what this holds them
 * to is that the second is refused where the value is made rather than carried into a document that
 * reads one number against the order of another.
 *
 * <p>Where the number can be dropped it has been, and there is nothing to check: a reader holding
 * only the orders is one this cannot be asked of.
 */
class OrdersAreHeldBesideTheNumberTheyAreOfTest {

    private static final NumericTerm.ValueOf CHARGE =
            new NumericTerm.ValueOf(TermPath.of("r").then("charge"));

    private static final NumericTerm.ValueOf CEILING =
            new NumericTerm.ValueOf(TermPath.of("r").then("ceiling"));

    private static final TermOrders OF_THE_CEILING =
            TermOrdersFixtures.itself(CEILING, Carrier.WHOLE);

    @Test
    void aClassOfACountIsNotBuiltOnAnotherNumbersOrders() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new Recognition.OfACount(CHARGE, OF_THE_CEILING,
                        new Recognition.CountIs.At(Count.of(1))));

        assertTrue(refused.getMessage().contains("charge")
                && refused.getMessage().contains("ceiling"), refused.getMessage());
    }

    @Test
    void norIsALineAComparisonDrew() {
        assertThrows(IllegalArgumentException.class,
                () -> new ComparedLine(CHARGE, Count.of(1), OF_THE_CEILING,
                        new souther.compiler.check.ComparisonClaim.Cut(
                                souther.compiler.numeric.Towards.BELOW, true)));
    }

    @Test
    void norIsACoordinateOfABorder() {
        assertThrows(IllegalArgumentException.class,
                () -> new BorderQuantity.OfACoordinate("weigh", CHARGE, OF_THE_CEILING));
    }

    /**
     * And a table from a number to its orders is one whose entries are about their own keys.
     *
     * <p>The key set agreeing says the table is about the right numbers and says nothing about
     * which of them each answer came from: a table with two ends swapped has exactly the same keys,
     * and every check the form and the key set can make passes.
     */
    @Test
    void norAreTheEntriesOfAFormsTable() {
        Map<NumericTerm, TermOrders> swapped = Map.of(
                CHARGE, OF_THE_CEILING,
                CEILING, TermOrdersFixtures.itself(CHARGE, Carrier.WHOLE));

        assertThrows(IllegalArgumentException.class,
                () -> new BorderQuantity.OverAForm("weigh",
                        new souther.compiler.numeric.LinearForm<>(
                                java.math.BigDecimal.ZERO,
                                Map.of(CHARGE, java.math.BigDecimal.ONE,
                                        CEILING, java.math.BigDecimal.ONE.negate())),
                        swapped));
    }

    /** And the pair says which number it is of, which is what all of the above read. */
    @Test
    void theOrdersSayWhichNumberTheyAreOf() {
        assertEquals(CEILING, OF_THE_CEILING.term());
    }
}
