package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeView;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.check.ValueAsked;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedRuns;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The keys a map is asked to hold, and the numbers the value under each is to be among, are
 * resolved into entries in {@link EntriesAsked} and nowhere else.
 *
 * <p>Every demand on one key is one entry, and the numbers asked of its value are the range every
 * demand leaves. Where the plan placed an element, the keys held are the key of that one entry;
 * where it placed none, each is an entry of its own.
 */
class TheEntriesAMapIsAskedToHoldAreResolvedInOnePlaceTest {

    private static final RuleReadingSource NONE =
            RuleReadings.ofNoClauseFiled(Symbols.none(DefaultStdlib.get()));

    private static final RuleReadingContext READING =
            RuleReadingContext.unshared(NONE, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);

    private static final FixtureTemplate A = FixtureTemplate.string("a");
    private static final FixtureTemplate B = FixtureTemplate.string("b");

    private static Shape.Mapping mapTo(Type value) {
        return (Shape.Mapping) TypeView.asWritten(new Type.MapOf(Type.STRING, value),
                NONE.symbols(), NONE.kinds(), NONE.sums()).shape();
    }

    private static ValueAsked exactly(String number) {
        Count at = Count.of(new BigDecimal(number));
        return ValueAsked.at(ValueAsked.THE_VALUE, OrderedRuns.of(
                new OrderedInterval(Endpoint.inclusive(at), Endpoint.inclusive(at))));
    }

    private static ValueAsked between(String low, String high) {
        return ValueAsked.at(ValueAsked.THE_VALUE, OrderedRuns.of(new OrderedInterval(
                Endpoint.exclusive(Count.of(new BigDecimal(low))),
                Endpoint.exclusive(Count.of(new BigDecimal(high))))));
    }

    private static ContainerContents.KeyAsked key(FixtureTemplate key, ValueAsked range) {
        return new ContainerContents.KeyAsked(key, Optional.ofNullable(range));
    }

    /** Where the plan placed no element, each key held is an entry of its own, over the value the
     *  rules name for it. */
    @Test
    void keysHeldWithNoElementPlacedAreEntriesOfTheirOwn() {
        EntriesAsked entries = EntriesAsked.of(mapTo(Type.DECIMAL), null, null,
                List.of(key(A, exactly("1")), key(B, exactly("2"))), List.of(), READING);

        assertNotNull(entries);
        assertNull(entries.placed());
        assertEquals(List.of("\"a\"", "\"b\""),
                entries.others().stream().map(each -> each.key().text()).toList());
        assertEquals(List.of("1m", "2m"),
                entries.others().stream().map(each -> each.value().text()).toList());
        assertEquals(List.of("1m", "2m"), entries.written().stream()
                .map(FixtureTemplate::text).toList());
    }

    /** An element placed is the one entry some entry is: two keys are held of it, or none. */
    @Test
    void twoKeysHeldOfTheOneEntryAPlacedElementIsFiledUnderAreNoMap() {
        FixtureTemplate element = FixtureTemplate.decimal(new BigDecimal("1"));

        assertNull(EntriesAsked.of(mapTo(Type.DECIMAL), null, element,
                List.of(key(A, null), key(B, null)), List.of(), READING));
        assertNotNull(EntriesAsked.of(mapTo(Type.DECIMAL), null, element,
                List.of(key(A, null), key(A, null)), List.of(), READING));
    }

    /** The value asked of the entry a placed element is filed under is that element's. */
    @Test
    void theNumberAskedOfThePlacedEntryIsTheElementsOrNoMap() {
        FixtureTemplate one = FixtureTemplate.decimal(new BigDecimal("1"));

        EntriesAsked agreeing = EntriesAsked.of(mapTo(Type.DECIMAL), null, one,
                List.of(key(A, exactly("1"))), List.of(), READING);
        assertNotNull(agreeing);
        assertEquals("1m", agreeing.placed().value().text());

        assertNull(EntriesAsked.of(mapTo(Type.DECIMAL), null, one,
                List.of(key(A, exactly("2"))), List.of(), READING));
    }

    /** Every demand on a key is one entry, whose value is among what they all leave. */
    @Test
    void demandsOnOneKeyAreOneEntryAmongWhatTheyAllLeave() {
        EntriesAsked entries = EntriesAsked.of(mapTo(Type.DECIMAL), null, null,
                List.of(key(A, between("5", "7"))), List.of(key(A, between("6", "9"))), READING);

        assertNotNull(entries);
        assertEquals(1, entries.others().size());
        BigDecimal number = new BigDecimal(entries.others().getFirst().value().text()
                .replace("m", ""));
        assertTrue(number.compareTo(new BigDecimal("6")) > 0
                && number.compareTo(new BigDecimal("7")) < 0, number::toString);
    }

    /** Demands that leave a value no number are no map. */
    @Test
    void demandsOnOneKeyThatLeaveItsValueNoNumberAreNoMap() {
        assertNull(EntriesAsked.of(mapTo(Type.DECIMAL), null, null,
                List.of(key(A, exactly("1"))), List.of(key(A, exactly("2"))), READING));
    }

    /** A range between two whole numbers holds no whole number, and a value that is one is not
     *  written; a decimal is written inside it. */
    @Test
    void aRangeBetweenTwoWholeNumbersIsWrittenOnlyAsADecimal() {
        assertNull(EntriesAsked.of(mapTo(Type.INT), null, null,
                List.of(key(A, between("5", "6"))), List.of(), READING));
        EntriesAsked decimal = EntriesAsked.of(mapTo(Type.DECIMAL), null, null,
                List.of(key(A, between("5", "6"))), List.of(), READING);
        assertNotNull(decimal);
        assertEquals("5.5m", decimal.others().getFirst().value().text());
    }
}
