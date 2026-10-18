package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.Extreme;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A number of an element read off its neighbours comes to what reading that element alone comes
 * to, asking its own value or key and then each element's in order, the way a reader of one
 * element did before the elements were put together once: the first field asked that held
 * nothing stops it, and failing that, what the values read say.
 *
 * <p>The reading alone is written out here from the values, field by field, and not through the
 * law it is held against. Held over every list of up to three elements over keys and values that
 * were read, not read for one reason or another, of no order, or not there at all.
 */
class ANumberOfAnElementStopsWhereReadingItAloneInTheOrderItAsksStopsTest {

    private static final TermPath XS = TermPath.of("xs");

    private static final Carrier WHOLE = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);

    private static final TypeSymbol TOUCH = TypeSymbols.declared(new TypeKey("demo", "Touch"));

    private static final List<ObservedValue> KEYS = List.of(new ObservedValue.Text("a"),
            new ObservedValue.Text("b"), new ObservedValue.Unknown("unreadable"),
            new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure()),
            new ObservedValue.Sequence(List.of()));

    private static final List<ObservedValue> VALUES = List.of(new ObservedValue.Integer(1),
            new ObservedValue.Integer(2), new ObservedValue.Unknown("unreadable"),
            new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure()));

    @Test
    void howOftenAValueOccursStopsWhereReadingItAloneStops() {
        NumericTerm.Multiplicity often = NumericTerm.Multiplicity.of(XS,
                XS.element().then("account"));
        TermOrders on = TermOrdersFixtures.orders(often, Carrier.TEXT, WHOLE);
        List<ObservedValue> elements = new ArrayList<>();
        for (ObservedValue key : KEYS) {
            elements.add(touch(Map.of("account", key)));
        }
        elements.add(touch(Map.of()));
        for (List<ObservedValue> every : listsOf(elements)) {
            for (ObservedValue own : every) {
                assertEquals(alone(on, own, every), together(on, own, every),
                        () -> own + " among " + every);
            }
        }
    }

    @Test
    void theEndOfAKeysValuesStopsWhereReadingItAloneStops() {
        List<ObservedValue> elements = new ArrayList<>();
        for (ObservedValue key : KEYS) {
            for (ObservedValue value : VALUES) {
                elements.add(touch(Map.of("account", key, "days", value)));
            }
            elements.add(touch(Map.of("account", key)));
        }
        for (ObservedValue value : VALUES) {
            elements.add(touch(Map.of("days", value)));
        }
        for (Extreme extreme : List.of(Extreme.LEAST, Extreme.GREATEST)) {
            NumericTerm.ExtremeOfItsKey keyed = NumericTerm.ExtremeOfItsKey.of(XS,
                    XS.element().then("account"), XS.element().then("days"), extreme);
            TermOrders on = TermOrdersFixtures.computed(keyed, WHOLE, WHOLE,
                    Map.of(keyed.keyField(), Carrier.TEXT));
            for (List<ObservedValue> every : listsOf(elements)) {
                for (ObservedValue own : every) {
                    assertEquals(alone(on, own, every), together(on, own, every),
                            () -> extreme + " " + own + " among " + every);
                }
            }
        }
    }

    private static TermOrders.Neighbouring<String> together(TermOrders on, ObservedValue own,
                                                          List<ObservedValue> every) {
        return on.together(TermOrdersFixtures.holding(on, every))
                .numberOf(TermOrdersFixtures.holding(on, own));
    }

    /**
     * The element read alone: its own value or key first, then the elements in order, each field
     * asked as the number needs it, and the first that held nothing recorded where it was asked.
     */
    private static TermOrders.Neighbouring<String> alone(TermOrders on, ObservedValue own,
                                                       List<ObservedValue> every) {
        Asked asked = new Asked(on);
        NumericTerm.Reading read = switch (on.amongItsNeighbours()) {
            case NumericTerm.Multiplicity often -> {
                ObservedValue mine = asked.at(own, often.placeField());
                List<ObservedValue> held = new ArrayList<>();
                for (ObservedValue each : every) {
                    held.add(asked.at(each, often.placeField()));
                }
                yield howOften(on.observed(), mine, held);
            }
            case NumericTerm.ExtremeOfItsKey keyed -> endOfItsKey(on, keyed, asked, own, every);
        };
        return asked.first != null ? new TermOrders.Neighbouring.HeldNothing<>(asked.first)
                : new TermOrders.Neighbouring.Read<>(read);
    }

    private static NumericTerm.Reading howOften(Carrier observed, ObservedValue own,
                                                List<ObservedValue> every) {
        NumericTerm.Reading firstStop = null;
        Map<Place, Long> counted = new HashMap<>();
        for (ObservedValue each : every) {
            Object where = placed(observed, each);
            if (where instanceof Place place) {
                counted.merge(place.canonical(), 1L, Long::sum);
            } else if (firstStop == null) {
                firstStop = (NumericTerm.Reading) where;
            }
        }
        Object mine = placed(observed, own);
        if (!(mine instanceof Place place)) {
            return (NumericTerm.Reading) mine;
        }
        return firstStop != null ? firstStop
                : new NumericTerm.Reading.Number(Count.of(counted.getOrDefault(
                        place.canonical(), 0L)));
    }

    private static NumericTerm.Reading endOfItsKey(TermOrders on,
                                                   NumericTerm.ExtremeOfItsKey keyed, Asked asked,
                                                   ObservedValue own, List<ObservedValue> every) {
        Carrier keyedOn = on.fieldCarrier(keyed.keyField());
        Object ownKey = placed(keyedOn, asked.at(own, keyed.keyField()));
        NumericTerm.Reading keyStopped = null;
        int keyStoppedAt = -1;
        Place end = null;
        NumericTerm.Reading valueStopped = null;
        int valueStoppedAt = -1;
        for (int at = 0; at < every.size(); at++) {
            Object itsKey = placed(keyedOn, asked.at(every.get(at), keyed.keyField()));
            if (!(itsKey instanceof Place place)) {
                if (keyStopped == null) {
                    keyStopped = (NumericTerm.Reading) itsKey;
                    keyStoppedAt = at;
                }
                continue;
            }
            if (!(ownKey instanceof Place mine) || !mine.sameAs(place) || valueStopped != null) {
                continue;
            }
            Object value = placed(on.observed(), asked.at(every.get(at), keyed.valueField()));
            if (value instanceof Place held) {
                end = end == null ? held : switch (keyed.extreme()) {
                    case Extreme.Least _ -> held.compareTo(end) < 0 ? held : end;
                    case Extreme.Greatest _ -> held.compareTo(end) > 0 ? held : end;
                };
            } else {
                valueStopped = (NumericTerm.Reading) value;
                valueStoppedAt = at;
            }
        }
        if (!(ownKey instanceof Place)) {
            return (NumericTerm.Reading) ownKey;
        }
        if (keyStopped != null && (valueStopped == null || keyStoppedAt < valueStoppedAt)) {
            return keyStopped;
        }
        if (valueStopped != null) {
            return valueStopped;
        }
        return end == null ? new NumericTerm.Reading.NotNumber() : new NumericTerm.Reading.Number(end);
    }

    /**
     * Where {@code on} puts {@code value}: a place, or the reading that says why none — holding
     * nothing is no number, a value not read whole at any depth of the newtypes around it is not
     * read, and one the order has no place for is unreadable.
     */
    private static Object placed(Carrier on, ObservedValue value) {
        if (value == null) {
            return new NumericTerm.Reading.NotNumber();
        }
        ObservedValue at = value;
        while (true) {
            Membership.Incomplete unread = Membership.unread(at);
            if (unread != null) {
                return new NumericTerm.Reading.Missing(unread.cause());
            }
            if (at instanceof ObservedValue.Constructed c && c.field("value") != null) {
                at = c.field("value");
            } else {
                break;
            }
        }
        Place place = on == null ? null : on.placeOf(at);
        return place != null ? place : new NumericTerm.Reading.Missing(
                Incompleteness.Cause.of(Incompleteness.Code.VALUE_UNREADABLE));
    }

    /** The fields asked of the elements, under the names {@code on} says are worn there, and why
     *  the first that held nothing held nothing. */
    private static final class Asked {

        private final TermOrders on;
        private String first;

        Asked(TermOrders on) {
            this.on = on;
        }

        ObservedValue at(ObservedValue element, ElementProjection field) {
            ObservedValue held = on.in(field, element);
            if (held == null && first == null) {
                first = "nothing at " + field;
            }
            return held;
        }
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

    private static ObservedValue touch(Map<String, ObservedValue> fields) {
        return new ObservedValue.Constructed(TOUCH, fields);
    }
}
