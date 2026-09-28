package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nothing having picked a number is not the numbers being the whole of what was asked.
 *
 * <p>The two go together wherever the question was read off the numbers themselves, which is what
 * a class of a row is. They part where the question could not be read at all: a set on an order
 * this reading does not have leaves the rules unreadable, so what is walked is some of something
 * nothing stated — and a walk of it has covered nothing, whoever did or did not pick a number out
 * of it.
 *
 * <p>Which is the difference between the two a proof about the model rests on. Read from the
 * absence of a candidate, a walk of numbers whose question nobody could state comes back saying
 * the rules leave no value of it.
 */
class AWalkOfNumbersOnNoOrderHasCoveredNoQuestionTest {

    private static final NumericSet A_RUN_OF_THEM = new NumericSet.InARun(
            new Band(Band.endAt(null, Bound.at(at(0), true), souther.compiler.numeric.Towards.ABOVE),
                    Band.endAt(null, Bound.at(at(10), true),
                            souther.compiler.numeric.Towards.BELOW)));

    private static final NumericSet ONE_OF_THEM = new NumericSet.At(Count.of(5));

    private static Level at(long value) {
        return new Level.OnACarrier(Carrier.WHOLE, Count.of(value));
    }

    /** A class read on its own order is what a walk of it covers. */
    @Test
    void aClassOnAnOrderIsWhatAWalkOfItCovers() {
        assertTrue(AskedAt.theClass(A_RUN_OF_THEM, Carrier.WHOLE).walkIsOfTheWholeQuestion(),
                "the numbers to walk are the ones the search is about");
    }

    /**
     * The same class with no order to read it on covers nothing, though nothing picked a number.
     *
     * <p>The one this exists for. What the rules leave is where they leave it on an order, so
     * without one there is nothing for the walk to have been of.
     */
    @Test
    void theSameClassWithNoOrderCoversNothing() {
        AskedAt asked = AskedAt.theClass(A_RUN_OF_THEM, null);

        assertEquals(null, asked.named(), "nothing picked a number out of it");
        assertFalse(asked.walkIsOfTheWholeQuestion(),
                "and walking it is still not walking a question anything stated");
        assertFalse(asked.about().isOneNumber(),
                "so nothing about it is one number either");
    }

    /** And the numbers to try are kept, so a caller that paid for one still tries it. */
    @Test
    void aNumberACallerPaidForIsStillTriedWhereTheOrderIsMissing() {
        AskedAt asked = AskedAt.aNumberOutOf(A_RUN_OF_THEM, Count.of(5), null);

        assertEquals(Count.of(5), asked.named(), "the number a caller named is the one to try");
        assertEquals(A_RUN_OF_THEM, asked.walking(), "out of the numbers it was named from");
        assertFalse(asked.walkIsOfTheWholeQuestion(), "and trying it covers no stated question");
    }

    /** A number picked out of a class covers the question only where the class is that number. */
    @Test
    void oneNumberCoversTheQuestionOnlyWhereTheQuestionIsThatNumber() {
        assertFalse(AskedAt.aNumberOutOf(A_RUN_OF_THEM, Count.of(5), Carrier.WHOLE)
                        .walkIsOfTheWholeQuestion(),
                "a run holds numbers beside the one that was tried");
        assertTrue(AskedAt.aNumberOutOf(ONE_OF_THEM, Count.of(5), Carrier.WHOLE)
                        .walkIsOfTheWholeQuestion(),
                "and a class of one number is the number tried");
    }

    /** A point tried with a number out of a wider item has covered the number and not the item. */
    @Test
    void aPointTriedWithANumberCoversTheItemOnlyWhereTheItemIsThatNumber() {
        NumbersAskedFor theRun = NumbersAskedFor.ofTheClass(A_RUN_OF_THEM, Carrier.WHOLE);
        NumbersAskedFor theOne = NumbersAskedFor.ofTheClass(ONE_OF_THEM, Carrier.WHOLE);

        assertFalse(AskedAt.oneNumberOf(theRun, Count.of(5)).walkIsOfTheWholeQuestion(),
                "the item holds every number beside the one the point was tried with");
        assertTrue(AskedAt.oneNumberOf(theOne, Count.of(5)).walkIsOfTheWholeQuestion(),
                "and an item of one number is covered by trying it");
    }

    /**
     * What the rules leave a term with no order is asked for without reading an order.
     *
     * <p>Where a rule holds such a term away from a value, the value is a place on the order it
     * has none of. Read anyway, this is an order's answer about a term that is on no order.
     */
    @Test
    void whatTheRulesLeaveIsAskedWithoutAnOrderToReadItOn() {
        NumericTerm.FromOnePosition term = new NumericTerm.ValueOf(TermPath.of("b"));
        OnTheWay.TakenIn away = new OnTheWay.TakenIn(
                new ConditionReportAnchor.WhereTheReadingMetIt("m", new ConditionOccurrence("b", 0)),
                new TakenConstraint.AwayFrom(term, Count.of(1)));

        NumbersAskedFor asked = NumbersAskedFor.askedOf(term, NothingTheRulesSay.REGION, null,
                List.of(away));

        assertFalse(asked.isOneNumber(), "nothing of the term's numbers was read");
    }
}
