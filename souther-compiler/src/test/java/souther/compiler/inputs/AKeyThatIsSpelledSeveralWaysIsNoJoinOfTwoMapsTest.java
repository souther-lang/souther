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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two maps hold a value under one key where the language says the keys are one, and the reading of
 * a join takes two observations to be one key only where they are equal.
 *
 * <p>That holds for the keys that cross the boundary, which the language writes one way. A decimal
 * key is the amount it stands for, so {@code 1.0} and {@code 1.00} are one key of a map and two
 * observations; read as two, the total of the products would be nought where the walk adds
 * some. Whether the keys can be told apart is asked before the join is read, and a join over keys
 * that cannot is not read at all: it is no number of the row, which a reading that came to nothing
 * would say, and it is not the sum of no products.
 */
class AKeyThatIsSpelledSeveralWaysIsNoJoinOfTwoMapsTest {

    private static final TermOrders ON = new TermOrders(
            new NumericTerm.ValueOf(TermPath.of("x")), new Carrier.Whole(), new Carrier.Whole());

    private static TermOrders.KeyedEntry entry(ObservedValue key, long value) {
        return new TermOrders.KeyedEntry(key, new ObservedValue.Integer(value));
    }

    @Test
    void keysTheLanguageWritesOneWayAreJoinedWhereTheyAreEqual() {
        List<TermOrders.KeyedEntry> first = List.of(
                entry(new ObservedValue.Text("a"), 2), entry(new ObservedValue.Text("b"), 5));
        List<TermOrders.KeyedEntry> second = List.of(entry(new ObservedValue.Text("a"), 3));
        assertTrue(ON.canTellTheKeysApart(first, second));
        assertEquals(new NumericTerm.Reading.Number(Count.of(6)), TermReading.joined(ON, first,
                second));
    }

    @Test
    void keysOfDecimalsCannotBeToldApartWhateverScaleTheyAreWrittenAt() {
        ObservedValue tenths = new ObservedValue.Decimal(new BigDecimal("1.0"));
        ObservedValue hundredths = new ObservedValue.Decimal(new BigDecimal("1.00"));
        for (ObservedValue other : List.of(tenths, hundredths)) {
            List<TermOrders.KeyedEntry> first = List.of(entry(tenths, 2));
            List<TermOrders.KeyedEntry> second = List.of(entry(other, 3));
            assertFalse(ON.canTellTheKeysApart(first, second), other::toString);
            // A join of them is not read, and so is not read as a total of nothing.
            assertThrows(IllegalArgumentException.class,
                    () -> TermReading.joined(ON, first, second), other::toString);
        }
    }

    @Test
    void aKeyThatHoldsADecimalCannotBeToldApartEither() {
        ObservedValue wornTenths = new ObservedValue.Constructed(
                TypeSymbols.declared(new TypeKey("demo", "Amount")),
                Map.of("value", new ObservedValue.Decimal(new BigDecimal("1.0"))));
        assertFalse(ON.canTellTheKeysApart(List.of(entry(wornTenths, 2)),
                List.of(entry(wornTenths, 3))));
    }

}
