package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A generated row refuses a decimal a model's own decimals put far enough apart in scale, rather
 * than spelling it out in full.
 *
 * <p>Exponent notation is not the answer for a generated row the way it is for a report: this
 * language's grammar has none for a {@code Decimal} literal, so a row written that way would not be
 * one a reader could paste back. Refusing it is the sound answer with less, the same one a candidate
 * the rules admit nothing at already gets — and it is asked here directly, rather than through a
 * whole compile, because the cost this refuses is one a single call already pays in full.
 */
class ADecimalOfExtremeScaleOffersNoGeneratedRowTest {

    @Test
    void anOrdinaryDecimalIsOfferedAsARow() {
        assertNotNull(FixtureTemplate.decimal(new BigDecimal("1.50")));
        assertNotNull(FixtureTemplate.decimal(BigDecimal.ZERO));
    }

    @Test
    void aDecimalOfExtremeScaleOffersNoRow() {
        assertNull(FixtureTemplate.decimal(new BigDecimal(BigInteger.ONE, 1_000_000)));
    }
}
