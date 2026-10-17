package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.Extreme;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A number of an element read off the elements beside it, read for every element in one pass, is
 * what each element reads when it is read alone: how often its value occurs, and the end of the
 * values of its key.
 *
 * <p>Held over lists where the elements read different numbers — values written to different
 * scales, several keys, keys holding several values — and over lists with a value no order puts
 * anywhere, where none of them is read.
 */
class ANumberOfEveryElementReadAtOnceIsWhatEachReadsAloneTest {

    private static final TermPath XS = TermPath.of("xs");

    private static final Carrier DECIMALS =
            Carrier.ofValue(Type.Prim.DECIMAL, DeclarationAccess.NONE);

    private static final Carrier WHOLE = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);

    @Test
    void howOftenEachValueOccursIsWhatEachCountsAlone() {
        TermOrders on = TermOrdersFixtures.itself(
                NumericTerm.Multiplicity.of(XS, XS.element()), DECIMALS);
        for (List<ObservedValue> every : List.of(
                List.of(decimal("1.0"), decimal("1.00"), decimal("2"), decimal("1")),
                List.of(decimal("3")),
                List.of(decimal("1"), new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure())))) {
            List<NumericTerm.Reading> alone = new ArrayList<>();
            for (ObservedValue own : every) {
                alone.add(on.readAmong(own, every));
            }
            assertEquals(alone, on.readEachAmong(every), () -> "over " + every);
        }
    }

    @Test
    void theEndOfEachKeysValuesIsWhatEachReadsAlone() {
        for (Extreme extreme : List.of(Extreme.LEAST, Extreme.GREATEST)) {
            NumericTerm.ExtremeOfItsKey term = NumericTerm.ExtremeOfItsKey.of(XS,
                    XS.element().then("account"), XS.element().then("days"), extreme);
            TermOrders on = TermOrdersFixtures.computed(term, WHOLE, WHOLE,
                    Map.of(term.keyField(), Carrier.TEXT));
            for (List<ObservedValue> every : List.of(
                    List.of(touch("a", 4), touch("b", 7), touch("a", 10), touch("b", 2),
                            touch("c", 5)),
                    List.of(touch("a", 1)),
                    List.of(touch("a", 1), unreadDays("a")),
                    List.of(touch("a", 1), unreadDays("b"), touch("b", 3)))) {
                List<Function<ElementProjection, ObservedValue>> each = new ArrayList<>();
                for (ObservedValue element : every) {
                    each.add(field -> field.in(element));
                }
                List<NumericTerm.Reading> alone = new ArrayList<>();
                for (Function<ElementProjection, ObservedValue> own : each) {
                    alone.add(on.readInItsOccurrence(own, each));
                }
                assertEquals(alone, on.readEachInItsOccurrence(each),
                        () -> extreme + " over " + every);
            }
        }
    }

    /**
     * Every list of up to three elements over keys and values some of which were not read, each
     * in its own way: what stops each element's reading is what stops it alone, and two values
     * stopped for two reasons are not reported as one of them.
     */
    @Test
    void everyElementReadsAloneWhatItReadsAtOnceWhateverWasNotRead() {
        List<ObservedValue> keys = List.of(new ObservedValue.Text("a"),
                new ObservedValue.Text("b"), new ObservedValue.Unknown("unreadable"),
                new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure()));
        List<ObservedValue> values = List.of(new ObservedValue.Integer(1),
                new ObservedValue.Integer(2), new ObservedValue.Unknown("unreadable"),
                new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure()));
        TermOrders counted = TermOrdersFixtures.itself(
                NumericTerm.Multiplicity.of(XS, XS.element()), Carrier.TEXT);
        for (List<ObservedValue> every : listsOf(keys)) {
            List<NumericTerm.Reading> alone = new ArrayList<>();
            for (ObservedValue own : every) {
                alone.add(counted.readAmong(own, every));
            }
            assertEquals(alone, counted.readEachAmong(every), () -> "counted over " + every);
        }
        List<ObservedValue> touches = new ArrayList<>();
        for (ObservedValue key : keys) {
            for (ObservedValue value : values) {
                touches.add(new ObservedValue.Constructed(
                        TypeSymbols.declared(new TypeKey("demo", "Touch")),
                        Map.of("account", key, "days", value)));
            }
        }
        for (Extreme extreme : List.of(Extreme.LEAST, Extreme.GREATEST)) {
            NumericTerm.ExtremeOfItsKey term = NumericTerm.ExtremeOfItsKey.of(XS,
                    XS.element().then("account"), XS.element().then("days"), extreme);
            TermOrders on = TermOrdersFixtures.computed(term, WHOLE, WHOLE,
                    Map.of(term.keyField(), Carrier.TEXT));
            for (List<ObservedValue> every : listsOf(touches)) {
                List<Function<ElementProjection, ObservedValue>> each = new ArrayList<>();
                for (ObservedValue element : every) {
                    each.add(field -> field.in(element));
                }
                List<NumericTerm.Reading> alone = new ArrayList<>();
                for (Function<ElementProjection, ObservedValue> own : each) {
                    alone.add(on.readInItsOccurrence(own, each));
                }
                assertEquals(alone, on.readEachInItsOccurrence(each), () -> extreme + " over " + every);
            }
        }
    }

    /** Two values not read for two reasons, each read as its own reason. */
    @Test
    void twoValuesNotReadAreEachReadAsWhatStoppedThem() {
        TermOrders counted = TermOrdersFixtures.itself(
                NumericTerm.Multiplicity.of(XS, XS.element()), Carrier.TEXT);
        List<ObservedValue> every = List.of(new ObservedValue.Unknown("unreadable"),
                new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure()));
        List<NumericTerm.Reading> read = counted.readEachAmong(every);
        assertEquals(List.of(counted.readAmong(every.get(0), every),
                counted.readAmong(every.get(1), every)), read);
        assertNotEquals(read.get(0), read.get(1), "two reasons are two readings");
    }

    /** A field of an element not read whole is what stopped it, and not a field it lacks. */
    @Test
    void aFieldOfAnElementNotReadWholeIsWhatStoppedIt() {
        ObservedValue cut = new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure());
        assertEquals(cut, new ElementProjection(List.of("days")).in(cut));
        assertNull(new ElementProjection(List.of("hours")).in(touch("a", 1)),
                "a field a value read whole does not hold is none");
    }

    /** Every list of one to three of {@code palette}, in every order and with repeats. */
    private static List<List<ObservedValue>> listsOf(List<ObservedValue> palette) {
        List<List<ObservedValue>> out = new ArrayList<>();
        List<List<ObservedValue>> shorter = List.of(List.of());
        for (int length = 1; length <= 3; length++) {
            List<List<ObservedValue>> longer = new ArrayList<>();
            for (List<ObservedValue> each : shorter) {
                for (ObservedValue one : palette) {
                    List<ObservedValue> grown = new ArrayList<>(each);
                    grown.add(one);
                    longer.add(grown);
                }
            }
            out.addAll(longer);
            shorter = longer;
        }
        return out;
    }

    /** What an element of another key holds, or failed to hold, is no part of this key's end. */
    @Test
    void aValueOfAnotherKeyThatWasNotReadLeavesThisKeysEndRead() {
        NumericTerm.ExtremeOfItsKey term = NumericTerm.ExtremeOfItsKey.of(XS,
                XS.element().then("account"), XS.element().then("days"), Extreme.LEAST);
        TermOrders on = TermOrdersFixtures.computed(term, WHOLE, WHOLE,
                Map.of(term.keyField(), Carrier.TEXT));
        List<ObservedValue> every = List.of(touch("a", 4), touch("a", 10), unreadDays("b"));
        List<Function<ElementProjection, ObservedValue>> each = new ArrayList<>();
        for (ObservedValue element : every) {
            each.add(field -> field.in(element));
        }
        NumericTerm.Reading four = on.readEachInItsOccurrence(each).getFirst();
        assertEquals(on.readInItsOccurrence(each.getFirst(), each), four);
        assertEquals(WHOLE.placeOf(new ObservedValue.Integer(4)),
                ((NumericTerm.Reading.Number) four).value());
    }

    private static ObservedValue unreadDays(String account) {
        return new ObservedValue.Constructed(TypeSymbols.declared(new TypeKey("demo", "Touch")),
                Map.of("account", new ObservedValue.Text(account),
                        "days", new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure())));
    }

    private static ObservedValue decimal(String written) {
        return new ObservedValue.Decimal(new BigDecimal(written));
    }

    private static ObservedValue touch(String account, long days) {
        return new ObservedValue.Constructed(TypeSymbols.declared(new TypeKey("demo", "Touch")),
                Map.of("account", new ObservedValue.Text(account),
                        "days", new ObservedValue.Integer(days)));
    }
}
