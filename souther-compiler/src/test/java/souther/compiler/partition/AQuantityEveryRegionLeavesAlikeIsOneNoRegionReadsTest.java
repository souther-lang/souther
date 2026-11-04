package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ReadingsOfEachValue;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which quantities are read the same values whatever the region
 * ({@link BorderQuantity#leftAlikeByEveryRegion}) is what no region is read for: a remainder of a
 * form over numbers of two positions, whose values together no region reads
 * ({@link ReadingsOfEachValue#of}), and not a remainder over one position, whose values a region
 * admits, nor a form, which a region leaves its terms.
 */
class AQuantityEveryRegionLeavesAlikeIsOneNoRegionReadsTest {

    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("a"));

    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));

    /** {@code Int.floorMod(form, 7)}. */
    private static BorderQuantity.RemainderOfAForm remainderOf(Map<NumericTerm, ExactRatio> coefs) {
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        coefs.keySet().forEach(term -> on.put(term, TermOrdersFixtures.itself(term,
                Carrier.WHOLE)));
        return new BorderQuantity.RemainderOfAForm("decide",
                new BorderQuantity.OverAForm("decide", new LinearForm<>(ExactRatio.ZERO, coefs),
                        on),
                BigInteger.ZERO, BigInteger.valueOf(7),
                new LinearForm<>(ExactRatio.ZERO, Map.of()), Map.of());
    }

    private static Map<NumericTerm, ExactRatio> aLess(NumericTerm other) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(A, ExactRatio.ONE);
        coefs.put(other, ExactRatio.ONE.negated());
        return coefs;
    }

    @Test
    void aRemainderOverTwoPositionsIsLeftAlike() {
        assertTrue(remainderOf(aLess(D)).leftAlikeByEveryRegion());
    }

    @Test
    void aRemainderOverOnePositionIsNot() {
        assertFalse(remainderOf(Map.of(A, ExactRatio.of(3))).leftAlikeByEveryRegion(),
                "what one position's values come to is what a region admits of them");
    }

    @Test
    void aFormIsNot() {
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(A, TermOrdersFixtures.itself(A, Carrier.WHOLE));
        assertFalse(new BorderQuantity.OverAForm("decide",
                new LinearForm<>(ExactRatio.ZERO, Map.of(A, ExactRatio.ONE)), on)
                .leftAlikeByEveryRegion());
    }

    /**
     * What the answer rests on: the values of numbers of two positions together are read of no
     * region, however few values each position admits; those of one position are.
     */
    @Test
    void theValuesOfTwoPositionsTogetherAreReadOfNone() {
        ValueSet few = new ValueSet.Finite(Set.of(Value.number(1), Value.number(2)));
        assertNull(ReadingsOfEachValue.of(few, List.of(
                TermOrdersFixtures.itself(A, Carrier.WHOLE),
                TermOrdersFixtures.itself(D, Carrier.WHOLE))));
        assertNotNull(ReadingsOfEachValue.of(few, List.of(
                TermOrdersFixtures.itself(A, Carrier.WHOLE))));
    }
}
