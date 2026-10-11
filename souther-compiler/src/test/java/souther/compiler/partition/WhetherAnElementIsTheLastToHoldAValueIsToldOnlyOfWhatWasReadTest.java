package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An element is the last to hold a value where every element after it was read and holds another,
 * and is not where one after it was read and holds the same. What could not be read shows neither.
 *
 * <p>A value that an observation could not keep, or could not read back, is no value: it is not
 * equal to another and it is not unequal. Compared as the placeholder it is, a key that was
 * stopped by a limit would be taken for a key nobody else holds, and the entry a lookup answers
 * would be called the last of its key on the strength of not having looked.
 */
class WhetherAnElementIsTheLastToHoldAValueIsToldOnlyOfWhatWasReadTest {

    private static final String MODEL = """
            module g

            data Row = { sku: String, qty: Int }

            behavior decide : (rows: List<Row>) -> Row
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            souther.compiler.values.AsACompilationAllows.admittedValues(),
            souther.compiler.values.AsACompilationAllows.whatARuleLeaves());

    private static final TermPath ROWS = TermPath.of("rows");

    private static final TermPath SKU = ROWS.element().then("sku");

    private static final ObservedValue A = new ObservedValue.Text("A");

    private static final ObservedValue B = new ObservedValue.Text("B");

    private static final ObservedValue TRUNCATED = new ObservedValue.Truncated();

    private static final ObservedValue UNREADABLE = new ObservedValue.Unknown("no");

    private static BorderQuantity.Lastness lastness(int element, ObservedValue... keys) {
        RuleReadingSource rules = RuleReadings.ofSource(MODEL);
        BehaviorInputs where = new BehaviorInputs(List.of("rows"),
                List.of(new Type.ListOf(named("Row"))), rules, POLICY);
        List<ObservedValue> rows = new java.util.ArrayList<>();
        for (ObservedValue key : keys) {
            rows.add(new ObservedValue.Constructed(sym("Row"),
                    Map.of("sku", key, "qty", new ObservedValue.Integer(1))));
        }
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(ROWS.element().then("qty"));
        StandingAtAPoint.Readings readings = StandingAtAPoint.readings(where,
                new ObservedInputs(List.of(new ObservedValue.Sequence(rows)),
                        new Generator.Watched.NoAccount(), new AnswerObservation.NotAnswered()),
                new BorderQuantity.OfACoordinate("decide", term,
                        TermOrdersFixtures.itself(term, new Carrier.Whole())));
        return readings.tried().get(element).lastToHold(ROWS, SKU);
    }

    private static BorderQuantity.Lastness couldNotTell(Incompleteness.Code why) {
        return new BorderQuantity.Lastness.CouldNotTell(ReadingGap.of(why));
    }

    private static final BorderQuantity.Lastness LAST = new BorderQuantity.Lastness.Last();

    private static final BorderQuantity.Lastness NOT_LAST = new BorderQuantity.Lastness.NotLast();

    @Test
    void ofTwoElementsOfOneKeyTheLaterIsTheLast() {
        assertEquals(NOT_LAST, lastness(0, A, A));
        assertEquals(LAST, lastness(1, A, A));
    }

    @Test
    void ofTwoKeysEachIsTheLastOfItsOwn() {
        assertEquals(LAST, lastness(0, A, B));
        assertEquals(LAST, lastness(1, A, B));
    }

    /** The control: what was not read in an element before this one says nothing of this one. */
    @Test
    void aKeyBeforeThisOneThatWasNotReadDoesNotKeepItFromBeingTheLast() {
        assertEquals(LAST, lastness(1, TRUNCATED, A));
        assertEquals(LAST, lastness(1, UNREADABLE, A));
    }

    @Test
    void anElementWhoseOwnKeyWasNotReadIsNotToldToBeTheLast() {
        assertEquals(couldNotTell(Incompleteness.Code.VALUE_TRUNCATED), lastness(0, TRUNCATED, A));
        assertEquals(couldNotTell(Incompleteness.Code.VALUE_UNREADABLE),
                lastness(0, UNREADABLE, A));
        assertEquals(couldNotTell(Incompleteness.Code.VALUE_TRUNCATED), lastness(1, A, TRUNCATED));
    }

    @Test
    void anElementWithAKeyAfterItThatWasNotReadIsNotToldToBeTheLast() {
        assertEquals(couldNotTell(Incompleteness.Code.VALUE_TRUNCATED), lastness(0, A, TRUNCATED));
        assertEquals(couldNotTell(Incompleteness.Code.VALUE_UNREADABLE),
                lastness(0, A, UNREADABLE));
    }

    /** A later element that was read and is equal settles that it is not, whatever else was not. */
    @Test
    void anEqualKeyAfterItThatWasReadSettlesItWhateverElseWasNotRead() {
        assertEquals(NOT_LAST, lastness(0, A, TRUNCATED, A));
        assertEquals(NOT_LAST, lastness(0, A, UNREADABLE, A));
    }

    /** And one that was read and is another key changes nothing of what was not read. */
    @Test
    void aKeyAfterItThatWasReadAndDiffersDoesNotSettleWhatWasNotRead() {
        assertEquals(couldNotTell(Incompleteness.Code.VALUE_TRUNCATED), lastness(0, A, B, TRUNCATED));
    }

    private static Type named(String data) {
        return Type.ref(sym(data));
    }

    private static TypeSymbol sym(String data) {
        return TypeSymbols.declared(new TypeKey("g", data));
    }
}
