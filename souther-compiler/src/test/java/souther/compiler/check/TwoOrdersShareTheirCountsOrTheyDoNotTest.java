package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which orders count in the same numbers, said once and both ways round.
 *
 * <p>What this decides is whether a rule comparing two positions is read as how far apart they stand
 * or as an arithmetic form over both of them. A form carries a conversion in its coefficients and a
 * distance has none, so a pair let through here that shares no counts would have its level measured
 * in a unit belonging to neither position.
 *
 * <p>A table and not a rule read back off the implementation. What a carrier's counts mean is a
 * decision — a second is a second of the day and a second of an epoch, and those are two decisions —
 * and a test that recomputed it would agree with whatever was written. The pairs below are the
 * answer, and the switch is exhaustive, so a ninth carrier fails to compile rather than falling into
 * whichever arm was written last.
 */
class TwoOrdersShareTheirCountsOrTheyDoNotTest {

    private static final TypeSymbol ONE_SUM = named("Colour");
    private static final TypeSymbol ANOTHER_SUM = named("Size");

    private static TypeSymbol named(String name) {
        return TypeSymbols.declared(new TypeKey("demo", name));
    }

    /** Every carrier there is, under a name to say which is which. */
    private static final Map<String, Carrier> ORDERS = orders();

    private static Map<String, Carrier> orders() {
        Map<String, Carrier> out = new LinkedHashMap<>();
        out.put("Int", Carrier.WHOLE);
        out.put("Decimal", Carrier.DENSE);
        out.put("Date", Carrier.DATE);
        out.put("DateTime", Carrier.MOMENT);
        out.put("Time", Carrier.TIME);
        out.put("Instant", Carrier.INSTANT);
        out.put("String", Carrier.TEXT);
        out.put("Colour", new Carrier.Ordinal(ONE_SUM, List.of(named("Red"))));
        out.put("Size", new Carrier.Ordinal(ANOTHER_SUM, List.of(named("Big"))));
        return out;
    }

    /**
     * The pairs whose counts are the same numbers, and there are no others.
     *
     * <p>Read as pairs rather than as an answer per carrier, since that is what the question is. A
     * whole number and a decimal are written on one line and step along it differently, which is a
     * fact about the values beside a distance rather than about the distance.
     */
    @Test
    void theseOrdersShareTheirCountsAndNoOthersDo() {
        List<String> shared = new ArrayList<>();
        ORDERS.forEach((here, one) -> ORDERS.forEach((there, other) -> {
            if (one.sharesCountSpaceWith(other)) {
                shared.add(here + "/" + there);
            }
        }));

        assertEquals(List.of(
                        "Int/Int", "Int/Decimal",
                        "Decimal/Int", "Decimal/Decimal",
                        "Date/Date",
                        // A date-time counts seconds from an epoch and a time of day counts seconds
                        // from midnight, so the same unit is two units of measurement from two
                        // origins. An instant counts nanoseconds on the same timeline a date-time is
                        // on, which is the other way for two orders to be one unit short of sharing
                        // a number: told apart by whether one value converts to the other, both
                        // pairs would be here.
                        "DateTime/DateTime",
                        "Time/Time",
                        "Instant/Instant",
                        // A string carries no count, so there is no number it shares with anything —
                        // itself included. Two strings still stand in an order and still meet, and
                        // that is `counts()`'s answer rather than this one's.
                        "Colour/Colour",
                        "Size/Size"),
                shared, "the orders whose counts are one arithmetic");
    }

    /**
     * The pairs a rule can compare two positions on, which is those and the one with no counts.
     *
     * <p>The question a reading of a comparison actually asks, and the reason the one above is not
     * made reflexive to answer it. Two strings stand one above the other and no number apart, so the
     * pair is here and is not up there — and a caller that measured how far apart they stand would
     * be reading this answer as that one.
     */
    @Test
    void theseOrdersCanBeComparedAgainstEachOther() {
        List<String> compared = new ArrayList<>();
        ORDERS.forEach((here, one) -> ORDERS.forEach((there, other) -> {
            if (one.standsAgainst(other)) {
                compared.add(here + "/" + there);
            }
        }));

        assertEquals(List.of(
                        "Int/Int", "Int/Decimal",
                        "Decimal/Int", "Decimal/Decimal",
                        "Date/Date",
                        "DateTime/DateTime",
                        "Time/Time",
                        "Instant/Instant",
                        "String/String",
                        "Colour/Colour",
                        "Size/Size"),
                compared, "the orders a rule can compare two positions on");
    }

    /** And neither answer depends on which of the two is asked. */
    @Test
    void neitherOrderOfAPairAnswersDifferently() {
        List<String> disagreed = new ArrayList<>();
        ORDERS.forEach((here, one) -> ORDERS.forEach((there, other) -> {
            if (one.sharesCountSpaceWith(other) != other.sharesCountSpaceWith(one)
                    || one.standsAgainst(other) != other.standsAgainst(one)) {
                disagreed.add(here + "/" + there);
            }
        }));

        assertEquals(List.of(), disagreed,
                "what two orders are to each other is a fact about the pair, not about which one"
                        + " was asked");
    }
}
