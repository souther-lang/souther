package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.DecimalPoints;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.partition.ContainersAddingUp.Ends;
import souther.compiler.partition.ContainersAddingUp.Split;
import souther.compiler.partition.ContainersAddingUp.Spread;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The scale of the total of a list a row holds is no more than the places a row is built at,
 * because the builder writes every element through {@link DecimalPoints#writtenForARow}.
 *
 * <p>The places are the generation's budget and bound which lists are tried, not which decimals
 * there are: a start the rules name at more places than that is a list nothing builds, which is a
 * row not built and not a value that does not exist.
 */
class AListATotalIsTheSumOfIsWrittenAtNoMorePlacesThanARowIsBuiltAtTest {

    private static final Carrier DENSE = new Carrier.Dense();

    /** The start every element moves from is written to more places than a row is built at, so
     *  the shares are, and no list is built. */
    @Test
    void aStartPastThePlacesARowIsBuiltAtBuildsNoList() {
        Count start = Count.of(new BigDecimal(BigInteger.ONE,
                DecimalPoints.PLACES_A_ROW_IS_BUILT_AT + 1));
        Ends ends = Ends.of(new NumericDomain.Bounds(Endpoint.inclusive(start), null), DENSE);
        for (Spread how : Spread.values()) {
            assertFalse(ContainersAddingUp.splitting(new BigDecimal("1.1"), 3, ends, how, DENSE)
                            instanceof Split.Some,
                    "no list is built at " + (DecimalPoints.PLACES_A_ROW_IS_BUILT_AT + 1)
                            + " places (" + how + ")");
        }
    }

    /** Within them, every element is written at no more. */
    @Test
    void aStartWithinThemBuildsElementsWithinThem() {
        Count start = Count.of(new BigDecimal(BigInteger.ONE,
                DecimalPoints.PLACES_A_ROW_IS_BUILT_AT));
        Ends ends = Ends.of(new NumericDomain.Bounds(Endpoint.inclusive(start), null), DENSE);
        Split split = ContainersAddingUp.splitting(new BigDecimal("1.1"), 3, ends, Spread.LEVEL,
                DENSE);
        for (BigDecimal each : assertInstanceOf(Split.Some.class, split).values()) {
            assertTrue(each.scale() <= DecimalPoints.PLACES_A_ROW_IS_BUILT_AT, each.toString());
        }
    }

    /** A number is written at one scale, whichever scale it was stated at: the fewest places
     *  there are, so nought at the greatest scale is nought, and no row holds it as that. */
    @Test
    void aNumberIsWrittenAtOneScaleOnly() {
        assertEquals(Optional.of(BigDecimal.ZERO), written(new BigDecimal(BigInteger.ZERO,
                Integer.MAX_VALUE)));
        assertEquals(Optional.of(0), written(new BigDecimal("4.0")).map(BigDecimal::scale));
        assertEquals(Optional.of(2), written(new BigDecimal("4.25")).map(BigDecimal::scale));
    }

    /** And at no more places than a row is built at: past them it is no row's. */
    @Test
    void aNumberPastThePlacesARowIsBuiltAtIsNoRows() {
        assertEquals(Optional.empty(), written(new BigDecimal(BigInteger.ONE,
                DecimalPoints.PLACES_A_ROW_IS_BUILT_AT + 1)));
        assertTrue(written(new BigDecimal(BigInteger.ONE,
                DecimalPoints.PLACES_A_ROW_IS_BUILT_AT)).isPresent());
    }

    private static Optional<BigDecimal> written(BigDecimal number) {
        return switch (DecimalPoints.writtenForARow(ExactRatio.of(number))) {
            case ExactAnswer.Held<Optional<BigDecimal>> held -> held.value();
            case ExactAnswer.Unheld<Optional<BigDecimal>> _ -> Optional.empty();
        };
    }
}
