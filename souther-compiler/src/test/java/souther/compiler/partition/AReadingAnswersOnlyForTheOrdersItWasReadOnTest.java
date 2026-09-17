package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A reading of a row answers for the orders it was read on, and refuses every other question.
 *
 * <p>A reading is a value now, so it can be handed to a quantity other than the one that made it.
 * What makes that a question rather than a mistake is what a reading is of: {@link
 * souther.compiler.inputs.TermOrders} and not a term, because the same position read on one order
 * and on another are two numbers and one of them is no number at all. A quantity answered from
 * orders it does not read on would be putting a row where a value it does not hold stands.
 *
 * <p><b>Two ways to get it, and the second is the one a term would not catch.</b> A reading of
 * another position is refused by having no entry for this one. A reading of <em>this</em> position
 * on another order has an entry under that term, and is a different number — so a reading asked for
 * by term would answer, and the verdict would come from the wrong decoding.
 *
 * <p>And the control is the same row read on the quantity's own orders, which settles it. Without
 * it a quantity that refuses everything would pass both of the above.
 */
class AReadingAnswersOnlyForTheOrdersItWasReadOnTest {

    private static final NumericTerm.ValueOf HERE = new NumericTerm.ValueOf(TermPath.of("here"));

    private static final NumericTerm.ValueOf THERE = new NumericTerm.ValueOf(TermPath.of("there"));

    private static final Criterion AT_A_HUNDRED =
            new Criterion.AtTheLevel(new Level.ACount(Count.of(100)));

    @Test
    void aRowReadOnTheQuantitysOwnOrdersIsAnswered() {
        BorderQuantity counted = coordinate(HERE, new Carrier.Whole());

        assertEquals(BorderQuantity.Stands.YES,
                counted.standsAt(AT_A_HUNDRED, counted.read(row(100))),
                "the row holds the number the line is at, read on the order it is written on");
    }

    @Test
    void aReadingOfAnotherPositionIsRefused() {
        BorderQuantity here = coordinate(HERE, new Carrier.Whole());
        BorderQuantity there = coordinate(THERE, new Carrier.Whole());

        assertThrows(IllegalArgumentException.class,
                () -> here.standsAt(AT_A_HUNDRED, there.read(row(100))),
                "a reading of another position says nothing about where this one stands");
        assertThrows(IllegalArgumentException.class,
                () -> here.valuesOf(there.read(row(100))),
                "and the numbers are the same question, so the same answer");
    }

    @Test
    void aReadingOfThisPositionOnAnotherOrderIsRefused() {
        BorderQuantity counted = coordinate(HERE, new Carrier.Whole());
        BorderQuantity inDays = coordinate(HERE, new Carrier.Days());

        assertThrows(IllegalArgumentException.class,
                () -> inDays.standsAt(AT_A_HUNDRED, counted.read(row(100))),
                "the same position on another order is another number, and this is not read on"
                        + " that one");
        assertThrows(IllegalArgumentException.class,
                () -> inDays.valuesOf(counted.read(row(100))),
                "and the numbers are the same question, so the same answer");
    }

    /** What the row comes to on the other order, which is what the refusal above keeps out. */
    @Test
    void theTwoOrdersDoNotReadTheRowAlike() {
        BorderQuantity inDays = coordinate(HERE, new Carrier.Days());

        assertEquals(BorderQuantity.Stands.NO,
                inDays.standsAt(AT_A_HUNDRED, inDays.read(row(100))),
                "read on its own order the row is no number of it, so it stands at nothing — and"
                        + " answering it from the other reading would have said it stands");
    }

    private static BorderQuantity coordinate(NumericTerm.ValueOf term, Carrier carrier) {
        return new BorderQuantity.OfACoordinate("decide", term,
                TermOrdersFixtures.itself(term, carrier));
    }

    private static BorderQuantity.Observation row(long value) {
        return new BorderQuantity.Observation() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                return WalkResult.reached(
                        new ObservationAtPoint.Value(new ObservedValue.Integer(value)));
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a number of one position is not read over a run");
            }
        };
    }
}
