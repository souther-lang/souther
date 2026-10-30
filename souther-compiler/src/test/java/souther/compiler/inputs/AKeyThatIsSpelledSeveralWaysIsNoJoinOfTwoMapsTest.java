package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Two maps hold a value under one key where the language says the keys are one, and the reading of
 * a join takes two observations to be one key only where they are equal.
 *
 * <p>That holds for the keys that cross the boundary, which the language writes one way. A decimal
 * key is the amount it stands for, so {@code 1.0} and {@code 1.00} are one key of a map and two
 * observations; read as two, the total of the products would be nought where the walk adds
 * some. A join over keys that are not spelled one way is then no number, and is not read as the
 * sum of nothing.
 */
class AKeyThatIsSpelledSeveralWaysIsNoJoinOfTwoMapsTest {

    private static final TermOrders ON = new TermOrders(
            new NumericTerm.ValueOf(TermPath.of("x")), new Carrier.Whole(), new Carrier.Whole());

    private static TermOrders.KeyedEntry entry(ObservedValue key, long value) {
        return new TermOrders.KeyedEntry(key, new ObservedValue.Integer(value));
    }

    @Test
    void keysTheLanguageWritesOneWayAreJoinedWhereTheyAreEqual() {
        NumericTerm.Reading read = TermReading.joined(ON,
                List.of(entry(new ObservedValue.Text("a"), 2), entry(new ObservedValue.Text("b"), 5)),
                List.of(entry(new ObservedValue.Text("a"), 3)));
        assertEquals(new NumericTerm.Reading.Number(Count.of(6)), read);
    }

    @Test
    void keysOfDecimalsAreNoJoinWhateverScaleTheyAreWrittenAt() {
        ObservedValue tenths = new ObservedValue.Decimal(new BigDecimal("1.0"));
        ObservedValue hundredths = new ObservedValue.Decimal(new BigDecimal("1.00"));
        for (ObservedValue other : List.of(tenths, hundredths)) {
            assertInstanceOf(NumericTerm.Reading.NotNumber.class,
                    TermReading.joined(ON, List.of(entry(tenths, 2)), List.of(entry(other, 3))),
                    other::toString);
        }
    }

    @Test
    void aKeyThatHoldsADecimalIsNoJoinEither() {
        ObservedValue wornTenths = new ObservedValue.Constructed(
                TypeSymbols.declared(new TypeKey("demo", "Amount")),
                Map.of("value", new ObservedValue.Decimal(new BigDecimal("1.0"))));
        assertInstanceOf(NumericTerm.Reading.NotNumber.class,
                TermReading.joined(ON, List.of(entry(wornTenths, 2)), List.of(entry(wornTenths, 3))));
    }
}
