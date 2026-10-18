package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.Extreme;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A number of an element read off the elements beside it, with the elements put together once and
 * asked of every element in whatever order, is what each element reads with them put together for
 * it alone: how often its value occurs, and the end of the values of its key.
 *
 * <p>Held over lists where the elements read different numbers — values written to different
 * scales, several keys, keys holding several values — and over lists with a value no order puts
 * anywhere, or an element holding nothing at a field, where what stops each element is its own.
 */
class ANumberOfEveryElementReadAtOnceIsWhatEachReadsAloneTest {

    private static final TermPath XS = TermPath.of("xs");

    private static final Carrier DECIMALS =
            Carrier.ofValue(Type.Prim.DECIMAL, DeclarationAccess.NONE);

    private static final Carrier WHOLE = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);

    private static final TypeSymbol TOUCH = TypeSymbols.declared(new TypeKey("demo", "Touch"));

    private static final NumericTerm.ExtremeOfItsKey LEAST = NumericTerm.ExtremeOfItsKey.of(XS,
            XS.element().then("account"), XS.element().then("days"), Extreme.LEAST);

    @Test
    void howOftenEachValueOccursIsWhatEachCountsAlone() {
        TermOrders on = TermOrdersFixtures.itself(
                NumericTerm.Multiplicity.of(XS, XS.element()), DECIMALS);
        for (List<ObservedValue> every : List.of(
                List.of(decimal("1.0"), decimal("1.00"), decimal("2"), decimal("1")),
                List.of(decimal("3")),
                List.of(decimal("1"), new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure())))) {
            eachReadsAtOnceWhatItReadsAlone(on, every);
        }
    }

    @Test
    void theEndOfEachKeysValuesIsWhatEachReadsAlone() {
        for (Extreme extreme : List.of(Extreme.LEAST, Extreme.GREATEST)) {
            TermOrders on = keyed(extreme);
            for (List<ObservedValue> every : List.of(
                    List.of(touch("a", 4), touch("b", 7), touch("a", 10), touch("b", 2),
                            touch("c", 5)),
                    List.of(touch("a", 1)),
                    List.of(touch("a", 1), unreadDays("a")),
                    List.of(touch("a", 1), unreadDays("b"), touch("b", 3)))) {
                eachReadsAtOnceWhatItReadsAlone(on, every);
            }
        }
    }

    /**
     * Every list of up to three elements over keys and values some of which were not read and
     * some of which are not there, each in its own way: what stops each element's reading is what
     * stops it alone, and two values stopped for two reasons are not reported as one of them.
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
            eachReadsAtOnceWhatItReadsAlone(counted, every);
        }
        List<ObservedValue> touches = new ArrayList<>();
        for (ObservedValue key : keys) {
            for (ObservedValue value : values) {
                touches.add(touch(key, value));
            }
            touches.add(new ObservedValue.Constructed(TOUCH, Map.of("account", key)));
        }
        for (ObservedValue value : values) {
            touches.add(new ObservedValue.Constructed(TOUCH, Map.of("days", value)));
        }
        for (Extreme extreme : List.of(Extreme.LEAST, Extreme.GREATEST)) {
            TermOrders on = keyed(extreme);
            for (List<ObservedValue> every : listsOf(touches)) {
                eachReadsAtOnceWhatItReadsAlone(on, every);
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
        List<TermOrders.Neighbouring<String>> read =
                eachReadsAtOnceWhatItReadsAlone(counted, every);
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

    /** What an element of another key holds, or failed to hold, is no part of this key's end. */
    @Test
    void aValueOfAnotherKeyThatWasNotReadLeavesThisKeysEndRead() {
        TermOrders on = keyed(Extreme.LEAST);
        List<ObservedValue> every = List.of(touch("a", 4), touch("a", 10), unreadDays("b"),
                new ObservedValue.Constructed(TOUCH,
                        Map.of("account", new ObservedValue.Text("b"))));
        assertEquals(read(4), eachReadsAtOnceWhatItReadsAlone(on, every).getFirst());
    }

    /**
     * An element holding nothing where a number reads stops what reads it, before any value that
     * was not read: of its own key, its own value or any key.
     */
    @Test
    void whatHoldsNothingWhereItIsReadStopsEveryNumberThatReadsIt() {
        TermOrders on = keyed(Extreme.LEAST);
        ObservedValue noDays = new ObservedValue.Constructed(TOUCH,
                Map.of("account", new ObservedValue.Text("a")));
        ObservedValue noAccount = new ObservedValue.Constructed(TOUCH,
                Map.of("days", new ObservedValue.Integer(1)));
        List<TermOrders.Neighbouring<String>> ofAKey = eachReadsAtOnceWhatItReadsAlone(on,
                List.of(unreadDays("a"), noDays, touch("b", 3)));
        assertEquals(new TermOrders.Neighbouring.Read<String>(new NumericTerm.Reading.Missing(
                        Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED,
                                Limits.DEFAULT.nodesFigure()))),
                ofAKey.getFirst(), "the first of the key's values stops it, and nothing after");
        assertEquals(ofAKey.getFirst(), ofAKey.get(1),
                "a value of the key after one that was not read is never asked");
        assertEquals(read(3), ofAKey.get(2), "another key's nothing is no part of this key's end");
        List<TermOrders.Neighbouring<String>> ofAnyKey = eachReadsAtOnceWhatItReadsAlone(on,
                List.of(unreadDays("a"), noAccount, touch("b", 3)));
        assertEquals(new TermOrders.Neighbouring.HeldNothing<String>("nothing at account"),
                ofAnyKey.get(2), "an element without a key may be of any key");
        assertEquals(new TermOrders.Neighbouring.HeldNothing<String>("nothing at account"),
                ofAnyKey.getFirst(), "and holding nothing outranks a value that was not read");
        assertEquals(new TermOrders.Neighbouring.HeldNothing<String>("nothing at days"),
                eachReadsAtOnceWhatItReadsAlone(on, List.of(noDays, noAccount)).getFirst(),
                "a value of its key read before a key that holds nothing is the first");
        assertEquals(new TermOrders.Neighbouring.HeldNothing<String>("nothing at account"),
                eachReadsAtOnceWhatItReadsAlone(on, List.of(noAccount, noDays)).get(1),
                "a key that holds nothing read before a value of its key is the first");
    }

    /**
     * The values of a key are read only once one of its elements is asked about, and each of
     * them once however many of its elements are.
     */
    @Test
    void theValuesOfAKeyAreReadOnceAndOnlyWhenItIsAsked() {
        TermOrders on = keyed(Extreme.LEAST);
        List<ObservedValue> every = List.of(touch("a", 4), touch("b", 7), touch("a", 10),
                touch("b", 2));
        int[] valuesRead = new int[every.size()];
        List<Function<ElementProjection, TermOrders.Holding<String>>> each = new ArrayList<>();
        for (int at = 0; at < every.size(); at++) {
            int element = at;
            Function<ElementProjection, TermOrders.Holding<String>> held =
                    TermOrdersFixtures.holding(every.get(at));
            each.add(field -> {
                if (field.equals(LEAST.valueField())) {
                    valuesRead[element]++;
                }
                return held.apply(field);
            });
        }
        TermOrders.ElementsTogether<String> together = on.together(each);
        together.numberOf(each.get(0));
        together.numberOf(each.get(2));
        assertEquals(List.of(1, 0, 1, 0), counts(valuesRead), "only key a was asked about");
        together.numberOf(each.get(1));
        together.numberOf(each.get(3));
        together.numberOf(each.get(0));
        assertEquals(List.of(1, 1, 1, 1), counts(valuesRead), "each value read once");
    }

    /**
     * Asks {@code on}'s number of every one of {@code every} of one occurrence put together once,
     * first to last and last to first, and of each put together for it alone; all three answer
     * alike, and that answer is returned in order.
     */
    private static List<TermOrders.Neighbouring<String>> eachReadsAtOnceWhatItReadsAlone(
            TermOrders on, List<ObservedValue> every) {
        List<Function<ElementProjection, TermOrders.Holding<String>>> each =
                TermOrdersFixtures.holding(every);
        List<TermOrders.Neighbouring<String>> alone = new ArrayList<>();
        for (Function<ElementProjection, TermOrders.Holding<String>> own : each) {
            alone.add(on.together(each).numberOf(own));
        }
        TermOrders.ElementsTogether<String> forwards = on.together(each);
        List<TermOrders.Neighbouring<String>> first = new ArrayList<>();
        for (Function<ElementProjection, TermOrders.Holding<String>> own : each) {
            first.add(forwards.numberOf(own));
        }
        TermOrders.ElementsTogether<String> backwards = on.together(each);
        List<TermOrders.Neighbouring<String>> last = new ArrayList<>();
        for (Function<ElementProjection, TermOrders.Holding<String>> own : each.reversed()) {
            last.add(backwards.numberOf(own));
        }
        Collections.reverse(last);
        assertEquals(alone, first, () -> "first to last over " + every);
        assertEquals(alone, last, () -> "last to first over " + every);
        return alone;
    }

    /** The number {@code whole}, read. */
    private static TermOrders.Neighbouring<String> read(long whole) {
        return new TermOrders.Neighbouring.Read<>(
                new NumericTerm.Reading.Number(WHOLE.placeOf(new ObservedValue.Integer(whole))));
    }

    private static TermOrders keyed(Extreme extreme) {
        NumericTerm.ExtremeOfItsKey term = NumericTerm.ExtremeOfItsKey.of(XS,
                XS.element().then("account"), XS.element().then("days"), extreme);
        return TermOrdersFixtures.computed(term, WHOLE, WHOLE,
                Map.of(term.keyField(), Carrier.TEXT));
    }

    private static List<Integer> counts(int[] each) {
        List<Integer> out = new ArrayList<>();
        for (int one : each) {
            out.add(one);
        }
        return out;
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

    private static ObservedValue unreadDays(String account) {
        return touch(new ObservedValue.Text(account),
                new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure()));
    }

    private static ObservedValue decimal(String written) {
        return new ObservedValue.Decimal(new BigDecimal(written));
    }

    private static ObservedValue touch(String account, long days) {
        return touch(new ObservedValue.Text(account), new ObservedValue.Integer(days));
    }

    private static ObservedValue touch(ObservedValue account, ObservedValue days) {
        return new ObservedValue.Constructed(TOUCH, Map.of("account", account, "days", days));
    }
}
