package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A position a row wrote nothing at answers for the row, and outranks what stopped elsewhere.
 *
 * <p>Two things a quantity meets that both leave it no number, and they are not the same news. A
 * reading that was stopped is this compiler unable to find out where the row stands; a position the
 * row put nothing at is the row saying it has no value for this quantity, which is an answer. So the
 * second settles the row however much of the rest could not be read — a quantity over a position the
 * row wrote nothing at is a row that does not stand, not a row nobody could place.
 *
 * <p><b>Both ways round, where round is a way there is.</b> A rule that held only when the row's own
 * answer was reached first would be a rule about the order the terms were walked in. A pair's ends
 * are walked in the order it holds them, so the pair is written twice with them swapped and an
 * answer that turns on which came first fails one of them. A form's terms are walked in the order
 * its coefficients happen to hash into, which is nobody's to choose — so writing one twice with the
 * terms exchanged is the same walk, and what the two lines below hold is that the answer does not
 * depend on how the form was spelled.
 */
class APositionARowWroteNothingAtAnswersForTheRowTest {

    private static final TermPath NOTHING_WRITTEN = TermPath.of("lines").element().then("amount");

    private static final TermPath STOPPED = TermPath.of("fees").element().then("amount");

    private static final NumericTerm.ValueOf AT_THE_EMPTY =
            new NumericTerm.ValueOf(NOTHING_WRITTEN);

    private static final NumericTerm.ValueOf AT_THE_STOPPED = new NumericTerm.ValueOf(STOPPED);

    /** A second stopped position, since a distance runs between two and not one named twice. */
    private static final NumericTerm.ValueOf AT_ANOTHER_STOPPED =
            new NumericTerm.ValueOf(TermPath.of("levies").element().then("amount"));

    private static final Criterion AT_A_HUNDRED =
            new Criterion.AtTheLevel(new Level.ACount(Count.of(100)));

    /** The row's answer, however the form carrying the term is written. */
    @Test
    void aFormOverAPositionTheRowWroteNothingAtDoesNotStand() {
        assertEquals(BorderQuantity.Stands.NO,
                form(AT_THE_EMPTY, AT_THE_STOPPED).standsAt(AT_A_HUNDRED, oneOfEach()),
                "the row wrote nothing at a position the form is over, so it has no value here");
        assertEquals(BorderQuantity.Stands.NO,
                form(AT_THE_STOPPED, AT_THE_EMPTY).standsAt(AT_A_HUNDRED, oneOfEach()),
                "and the same with the two terms written the other way round");
    }

    /**
     * A pair with one end the row wrote nothing at says the same, whichever end it is.
     *
     * <p>The other quantity that reads more than one position, and it collects its reasons from
     * both ends before concluding. So it is asked here too rather than left to the form's answer:
     * two quantities are two places the rule can be got wrong.
     */
    @Test
    void aPairWithOneEndTheRowWroteNothingAtDoesNotStand() {
        assertEquals(BorderQuantity.Stands.NO,
                pair(AT_THE_EMPTY, AT_THE_STOPPED).standsAt(AT_A_HUNDRED, oneOfEach()),
                "an end the row wrote nothing at leaves the pair no distance to stand at");
        assertEquals(BorderQuantity.Stands.NO,
                pair(AT_THE_STOPPED, AT_THE_EMPTY).standsAt(AT_A_HUNDRED, oneOfEach()),
                "and the same with the ends swapped");
    }

    /**
     * And a quantity whose every term was stopped says so, which is the control.
     *
     * <p>Without it the two above pass for a quantity that answers that nothing stands whatever it
     * meets — which is the answer the row's own is being told apart from.
     */
    @Test
    void aQuantityStoppedAndNothingElseIsUndecided() {
        BorderQuantity.Stands undecided = BorderQuantity.Stands.couldNotTell(
                ReadingGap.of(Incompleteness.Code.VALUE_TRUNCATED));

        assertEquals(undecided,
                form(AT_THE_STOPPED, AT_THE_STOPPED).standsAt(AT_A_HUNDRED, oneOfEach()),
                "nothing here is the row's answer, so the point is one this could not tell about");
        assertEquals(undecided,
                pair(AT_THE_STOPPED, AT_ANOTHER_STOPPED).standsAt(AT_A_HUNDRED, oneOfEach()),
                "and the same of a pair whose ends were both stopped");
    }

    /** A row that wrote nothing at one position and a value the limits stopped at the other. */
    private static BorderQuantity.Observation oneOfEach() {
        return new BorderQuantity.Observation() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                return WalkResult.reached(NOTHING_WRITTEN.equals(path)
                        ? ObservationAtPoint.WROTE_NOTHING
                        : new ObservationAtPoint.Value(new ObservedValue.Truncated()));
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a number of one position is not read over a run");
            }
        };
    }

    private static BorderQuantity.OverAForm form(NumericTerm.ValueOf first,
                                                 NumericTerm.ValueOf second) {
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(first, ordersOf(first));
        on.put(second, ordersOf(second));
        return new BorderQuantity.OverAForm("decide",
                LinearForm.atom((NumericTerm) first).plus(LinearForm.atom((NumericTerm) second)),
                on);
    }

    private static BorderQuantity.Apart pair(NumericTerm.ValueOf on, NumericTerm.ValueOf against) {
        return new BorderQuantity.Apart("decide", ordersOf(on), ordersOf(against));
    }

    private static TermOrders ordersOf(NumericTerm.ValueOf term) {
        return TermOrdersFixtures.itself(term, new Carrier.Whole());
    }
}
