package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Scopes;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTimes;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Text;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.time.Instant;
import java.time.LocalDate;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Which types a rule can be read of, told apart from which types a value can be written at.
 *
 * <p>One type answered both questions, and the answer the smaller one needed was the larger one's.
 * A {@code Time} is ordered and its literals compare, so an invariant whose ends cannot both hold is
 * as plain there as anywhere; it went unrefused because deciding that needed a {@link Carrier}, and
 * a carrier owes a way back from its counts and a spacing besides. So a rule went unread for want of
 * machinery no reading of it uses.
 *
 * <p>The two are separate types now. {@link OrderScale} is what a rule is read against — a literal
 * onto the order, how the values are spaced, and where the order stops — and {@link Carrier} is that
 * with the writing added. Which types have which is one answer in one place: a carrier is a scale
 * that also writes, so nothing can call a type a carrier that the scale reading calls something
 * else.
 */
class ReadingARuleNeedsLessOfATypeThanWritingAValueDoesTest {

    private static final String MODEL = """
            module example.scales

            data Red
            data Green
            data Blue
            data Colour = Red | Green | Blue
            """;

    private static Symbols symbols() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        return Scopes.derived(compilation.db(), compilation.modules().get(0)).value();
    }

    private static Type colour() {
        return Type.ref(TypeSymbols.declared(new TypeKey("example.scales", "Colour")));
    }

    /**
     * A {@code Time} and an {@code Instant} are read and are not written.
     *
     * <p>The two the split exists for. Each is ordered, each has literals that compare, and neither
     * has been given the way back from a count that a line drawn at it would need — so each answers
     * the reading question and not the writing one.
     */
    @Test
    void theTwoTemporalsWithNoWayBackAreScalesAndNotCarriers() {
        Symbols symbols = symbols();

        assertNotNull(OrderScale.ofValue(Type.TIME, symbols), "a `Time`'s literals compare");
        assertNull(Carrier.ofValue(Type.TIME, symbols), "and no value is written back at one");

        assertNotNull(OrderScale.ofValue(Type.INSTANT, symbols), "an `Instant`'s literals compare");
        assertNull(Carrier.ofValue(Type.INSTANT, symbols), "and no value is written back at one");
    }

    /**
     * Every other ordered type is both, and is the same one under either question.
     *
     * <p>Asked of the scale reading and narrowed, rather than answered twice. Two readers deciding
     * which types have counts is what left a {@code Date} a carrier to one of them and not to
     * another, and a second answer here would be that again one level up.
     */
    @Test
    void aCarrierIsTheScaleReadingNarrowedAndNotASecondAnswer() {
        Symbols symbols = symbols();

        for (Type each : new Type[] {Type.INT, Type.DECIMAL, Type.DATE, Type.DATETIME,
                Type.STRING, colour()}) {
            OrderScale scale = OrderScale.ofValue(each, symbols);
            assertInstanceOf(Carrier.class, scale, each + " is written back at");
            assertEquals(scale, Carrier.ofValue(each, symbols),
                    each + " is one type under both questions");
        }

        assertNull(OrderScale.ofValue(Type.BOOL, symbols), "a `Bool` is not ordered");
        assertNull(OrderScale.ofValue(Type.RAW, symbols), "and neither is a `Raw`");
    }

    /**
     * Where each order stops, which is the third thing reading a rule needs.
     *
     * <p>Not derivable from the spacing and not the same question. A rule stating an end below the
     * least value of a scale admits nothing, and a reading starting every position at an unbounded
     * range has no way to find that out: {@code value < ""} leaves a range open below, which is a
     * range holding everything under a string that has nothing under it.
     */
    @Test
    void everyScaleSaysWhereItsOrderStops() {
        Symbols symbols = symbols();
        Map<Type, OrderedInterval> expected = new LinkedHashMap<>();
        expected.put(Type.INT, between(Count.of(Long.MIN_VALUE), Count.of(Long.MAX_VALUE)));
        expected.put(Type.DECIMAL, new OrderedInterval(null, null));
        expected.put(Type.DATE, between(Count.of(LocalDate.MIN.toEpochDay()),
                Count.of(LocalDate.MAX.toEpochDay())));
        expected.put(Type.DATETIME, between(DateTimes.MIN, DateTimes.MAX));
        expected.put(Type.STRING, new OrderedInterval(Endpoint.inclusive(Text.of("")), null));
        expected.put(Type.TIME, between(Count.of(0), Count.of(86399)));
        expected.put(Type.INSTANT, between(nanosOf(Instant.MIN), nanosOf(Instant.MAX)));
        expected.put(colour(), between(Count.of(0), Count.of(2)));

        expected.forEach((type, extent) -> assertEquals(extent,
                OrderScale.ofValue(type, symbols).extent(), "where " + type + " stops"));
    }

    private static OrderedInterval between(Count low, Count high) {
        return new OrderedInterval(Endpoint.inclusive(low), Endpoint.inclusive(high));
    }

    private static Count nanosOf(Instant at) {
        return Count.of(java.math.BigDecimal.valueOf(at.getEpochSecond())
                .multiply(java.math.BigDecimal.valueOf(1_000_000_000L))
                .add(java.math.BigDecimal.valueOf(at.getNano())));
    }
}
