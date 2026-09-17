package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.observe.ObservedValue;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row is walked once, and every question asked about it is asked of what that walk read.
 *
 * <p>Reading a row costs a walk of the body per position, and the answers wanted of one row are more
 * than one: what its numbers are, and whether they stand at each of the lines a measure drew. Asked
 * of the row, each of those questions walks it; asked of a reading of it, they do not — which is why
 * {@link BorderQuantity#read} hands back what it read rather than an answer about it.
 *
 * <p><b>And the control is a second reading.</b> Without it, a quantity that walked nothing at all
 * would pass this: what the count has to tell apart is a walk not made twice from a walk not made.
 */
class ARowIsWalkedOnceHoweverManyQuestionsAreAskedOfItTest {

    private static final NumericTerm.ValueOf ONE_SIDE =
            new NumericTerm.ValueOf(TermPath.of("straw"));

    private static final NumericTerm.ValueOf THE_OTHER =
            new NumericTerm.ValueOf(TermPath.of("choco"));

    private static final Criterion AT_A_HUNDRED =
            new Criterion.AtTheLevel(new Level.ACount(Count.of(100)));

    private static final Criterion AT_A_THOUSAND =
            new Criterion.AtTheLevel(new Level.ACount(Count.of(1000)));

    @Test
    void readingARowWalksEachOfTheQuantitysPositionsOnce() {
        List<TermPath> walked = new ArrayList<>();

        form().read(row(walked));

        assertEquals(Map.of(ONE_SIDE.position(), 1, THE_OTHER.position(), 1), walksPer(walked),
                "each position of the form was walked, and each of them once");
    }

    @Test
    void askingAboutTheReadingWalksNothing() {
        List<TermPath> walked = new ArrayList<>();
        BorderQuantity.OverAForm form = form();
        QuantityReading reading = form.read(row(walked));

        form.standsAt(AT_A_HUNDRED, reading);
        form.valuesOf(reading);
        form.standsAt(AT_A_THOUSAND, reading);

        assertEquals(Map.of(ONE_SIDE.position(), 1, THE_OTHER.position(), 1), walksPer(walked),
                "what the row reads as was read once, and three questions were answered from it");
    }

    /**
     * And a row read a second time is walked a second time, which is the control.
     *
     * <p>The saving above is a walk not made, and a walk nobody could have made looks the same from
     * the count. This is what says the positions above were ones a walk of the row reaches.
     */
    @Test
    void aRowReadAgainIsWalkedAgain() {
        List<TermPath> walked = new ArrayList<>();
        BorderQuantity.OverAForm form = form();
        BorderQuantity.Observation row = row(walked);

        form.read(row);
        form.read(row);

        assertEquals(Map.of(ONE_SIDE.position(), 2, THE_OTHER.position(), 2), walksPer(walked),
                "two readings of one row are two walks of it");
    }

    /** How many times each position was walked. Counted rather than listed: which order a form
     *  reads its terms in is the form's, and nothing here is about it. */
    private static Map<TermPath, Integer> walksPer(List<TermPath> walked) {
        Map<TermPath, Integer> counted = new LinkedHashMap<>();
        for (TermPath path : walked) {
            counted.merge(path, 1, Integer::sum);
        }
        return counted;
    }

    /** A row holding a number at each of the form's positions, recording every walk it is asked
     *  for. */
    private static BorderQuantity.Observation row(List<TermPath> walked) {
        return new BorderQuantity.Observation() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                walked.add(path);
                return WalkResult.reached(
                        new ObservationAtPoint.Value(new ObservedValue.Integer(50)));
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a number of one position is not read over a run");
            }
        };
    }

    private static BorderQuantity.OverAForm form() {
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(ONE_SIDE, ordersOf(ONE_SIDE));
        on.put(THE_OTHER, ordersOf(THE_OTHER));
        return new BorderQuantity.OverAForm("decide",
                LinearForm.atom((NumericTerm) ONE_SIDE)
                        .plus(LinearForm.atom((NumericTerm) THE_OTHER)),
                on);
    }

    private static TermOrders ordersOf(NumericTerm.ValueOf term) {
        return TermOrdersFixtures.itself(term, new Carrier.Whole());
    }
}
