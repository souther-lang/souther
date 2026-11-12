package souther.compiler.values;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number read back from a run as an integer and the same number read back as a decimal are one
 * observation of one {@link Value}, and the value sits at one place on the order of a position of
 * either kind.
 */
class TwoNumeralsOfOneNumberAreOneObservationOfOneValueTest {

    private static final ObservedValue AS_AN_INTEGER = new ObservedValue.Integer(1);
    private static final ObservedValue AS_A_DECIMAL = new ObservedValue.Decimal(new BigDecimal("1.00"));

    @Test
    void bothDenoteTheValueTheSourceWrites() {
        Value written = Value.number(new BigDecimal("1.0"));

        assertEquals(written, WrittenValues.denotedBy(AS_AN_INTEGER));
        assertEquals(written, WrittenValues.denotedBy(AS_A_DECIMAL));
        assertEquals(true, WrittenValues.denotes(AS_AN_INTEGER, written));
        assertEquals(true, WrittenValues.denotes(AS_A_DECIMAL, written));
    }

    @Test
    void aNumberOfAnotherValueIsNotIt() {
        assertEquals(false, WrittenValues.denotes(AS_A_DECIMAL, Value.number(2)));
        assertEquals(false, WrittenValues.denotes(AS_AN_INTEGER, Value.number(new BigDecimal("1.5"))));
    }

    @Test
    void aKindThatIsNotWrittenAlikeIsNeitherEqualNorUnequal() {
        assertNull(WrittenValues.denotes(new ObservedValue.Text("1"), Value.number(1)));
        assertNull(WrittenValues.denotes(AS_AN_INTEGER, Value.text("1")));
        assertNull(WrittenValues.denotes(new ObservedValue.Unknown("not run"), Value.number(1)));
    }

    @Test
    void aNewtypeIsTakenOffForAScalarAndNotForACase() {
        TypeSymbol amount = TypeSymbols.declared(new TypeKey("demo", "Amount"));
        ObservedValue worn = new ObservedValue.Constructed(amount, Map.of("value", AS_AN_INTEGER));

        assertEquals(true, WrittenValues.denotes(worn, Value.number(1)));
        assertNull(WrittenValues.denotes(worn, Value.of(amount)));
    }

    @Test
    void aFractionIsOnTheDenseOrderAndNotOnTheWholeOne() {
        Value fraction = Value.number(new BigDecimal("1.5"));

        assertNull(Carrier.WHOLE.placeOf(fraction));
        assertTrue(Carrier.DENSE.placeOf(fraction).sameAs(Count.of(new BigDecimal("1.5"))));
    }

    @Test
    void theValueAndItsObservationsSitAtOnePlaceOnEitherOrder() {
        for (Carrier carrier : new Carrier[] {Carrier.WHOLE, Carrier.DENSE}) {
            Place written = carrier.placeOf(Value.number(1));

            assertTrue(written.sameAs(carrier.placeOf(AS_AN_INTEGER)));
            assertTrue(written.sameAs(carrier.placeOf(AS_A_DECIMAL)));
        }
    }
}
