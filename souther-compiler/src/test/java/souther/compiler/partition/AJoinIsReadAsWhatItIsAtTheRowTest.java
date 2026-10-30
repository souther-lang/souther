package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.Carrier;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the products of the values two maps hold under one key come to at a row is read as what it
 * is, and where it cannot be read it says why, rather than being read as a number the row lacks.
 *
 * <p>Four things a join comes to at a row, and they are four answers: a total, which is nought
 * where the maps share no key; keys that the observation of them does not tell apart, which are
 * keys of a decimal; a value that was there and did not come back whole; and a row that wrote no
 * entry, which has nothing to total. Read as one answer, a reader is told that the row holds no
 * number where it holds one and this reading could not say which.
 */
class AJoinIsReadAsWhatItIsAtTheRowTest {

    private static final TermPath AGREED = TermPath.of("agreed");
    private static final TermPath PRICES = TermPath.of("prices");
    private static final RunSource.JoinedOccurrences JOINED =
            new RunSource.JoinedOccurrences(AGREED.element(), PRICES.element());

    private static final NumericTerm.TakenOver TOTAL = NumericTerm.TakenOver.of(
            ValueName.Stdlib.operation("List", "sum"), JOINED, Type.Prim.INT, NewtypeInners.NONE,
            Symbols.none(DefaultStdlib.get()));

    private static final TermOrders ON = TermOrdersFixtures.itself(TOTAL, new Carrier.Whole());

    /** One entry of a map: the key it is filed under and the value filed. */
    private record Entry(ObservedValue key, ObservedValue value) { }

    private static ObservedValue text(String key) {
        return new ObservedValue.Text(key);
    }

    private static ObservedValue whole(long value) {
        return new ObservedValue.Integer(value);
    }

    private static Entry entry(ObservedValue key, ObservedValue value) {
        return new Entry(key, value);
    }

    /** A row holding two maps: {@code agreed} and {@code prices}, each as its entries. */
    private static BorderQuantity.Observation row(List<Entry> agreed, List<Entry> prices) {
        return new BorderQuantity.Observation() {
            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                throw new AssertionError("a join is read entry by entry: " + path);
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a join is read entry by entry: " + path);
            }

            @Override
            public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
                List<BorderQuantity.Observation> out = new ArrayList<>();
                for (Entry each : container.equals(AGREED) ? agreed : prices) {
                    out.add(entryOf(container, each));
                }
                return WalkResult.reached(out);
            }
        };
    }

    /** An entry of the map at {@code map}, read at its key and at its value. */
    private static BorderQuantity.Observation entryOf(TermPath map, Entry entry) {
        return new BorderQuantity.Observation() {
            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                if (path.equals(map.key())) {
                    return WalkResult.reached(new ObservationAtPoint.Value(entry.key()));
                }
                if (path.equals(map.element())) {
                    return WalkResult.reached(new ObservationAtPoint.Value(entry.value()));
                }
                return WalkResult.reached(ObservationAtPoint.WROTE_NOTHING);
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("an entry is read at its key and its value: " + path);
            }

            @Override
            public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
                throw new AssertionError("an entry holds no container: " + container);
            }
        };
    }

    private static WhatATermRead read(List<Entry> agreed, List<Entry> prices) {
        return WhatATermRead.joined(ON, JOINED, row(agreed, prices));
    }

    @Test
    void theProductsUnderTheKeysBothMapsHoldAreAdded() {
        assertEquals(new WhatATermRead.Number(Count.of(6)),
                read(List.of(entry(text("a"), whole(2)), entry(text("b"), whole(5))),
                        List.of(entry(text("a"), whole(3)))));
    }

    @Test
    void mapsThatShareNoKeyHoldNoProductAndTotalNought() {
        assertEquals(new WhatATermRead.Number(Count.ZERO),
                read(List.of(entry(text("a"), whole(2))), List.of(entry(text("b"), whole(3)))));
    }

    @Test
    void mapsThatAreEmptyTotalNought() {
        assertEquals(new WhatATermRead.Number(Count.ZERO), read(List.of(), List.of()));
    }

    @Test
    void keysThatTheirObservationsDoNotTellApartAreKeysNotToldAndNotANumberTheRowLacks() {
        ObservedValue tenths = new ObservedValue.Decimal(new BigDecimal("1.0"));
        ObservedValue hundredths = new ObservedValue.Decimal(new BigDecimal("1.00"));
        assertEquals(new WhatATermRead.CameToNothing(ReadingGap.KEYS_NOT_TOLD),
                read(List.of(entry(tenths, whole(2))), List.of(entry(hundredths, whole(3)))));
    }

    @Test
    void aValueThatDidNotComeBackWholeIsWhatTheObservationMet() {
        ObservedValue unread = new ObservedValue.Unknown("nothing read it");
        assertEquals(new WhatATermRead.CameToNothing(ReadingGap.of(unread.cause())),
                read(List.of(entry(text("a"), unread)), List.of(entry(text("a"), whole(3)))));
    }
}
