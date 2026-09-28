package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Membership;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two places a number the exact arithmetic could not hold used to be misread once it was told
 * apart from a genuine refusal, each fixed for its own reason and both of the same shape: an
 * {@code Unheld} answer fell through into whatever the ordinary "no" already meant there.
 */
class ANumberTheExactArithmeticCouldNotHoldIsNeverReadAsADecidedAnswerTest {

    /**
     * {@link ContainersAddingUp.Ends#reaches} wrote its last line as an {@code instanceof Held}
     * pattern used directly as the method's boolean answer, so an {@code Unheld} distance — which
     * does not match the pattern — silently became {@code false}: the one claim its own doc says an
     * unheld distance must never support, since {@code false} is what proves no arrangement reaches
     * the total.
     */
    @Test
    void anEndTheExactArithmeticCannotHoldTheDistanceToNeverProvesNoArrangementReachesIt() {
        ExactRatio from = ExactRatio.ONE;
        // A value so far apart from `from` in scale that computing their difference needs more
        // room than a long exponent leaves, which is what stands for the two decimals a model wrote
        // near opposite ends of the scale range this compiler holds.
        ExactRatio farBeyondWhatALongExponentBridges =
                new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MIN_VALUE + 1, 0);
        ContainersAddingUp.Ends ends = new ContainersAddingUp.Ends(
                from, null, farBeyondWhatALongExponentBridges, NumericDomain.Bounds.OPEN);

        assertTrue(ends.reaches(BigDecimal.valueOf(2), 1),
                "the exact arithmetic could not hold the distance to the end, and that is never a"
                        + " proof that no arrangement reaches the total");
    }

    /**
     * {@link InputClassifications#decided} used to have no arm for {@link Membership.NotWorkedOut}
     * beyond a thrown {@code IllegalStateException}, reachable from an ordinary rule bounding a
     * count taken as a sum over a {@code List<Decimal>} spaced far enough apart in scale. It now
     * answers {@link Classification.Unclassified} carrying
     * {@link Incompleteness.Code#VALUE_NOT_WORKED_OUT}, the same as any other class this measure
     * could not settle — not a crash, and not read as a class the value holds or does not.
     */
    @Test
    void aClassAskedACountItCouldNotWorkOutIsUndeterminedRatherThanACrashOrADecidedAnswer() {
        AxisId axis = new AxisId("overDecimals", "List.sum(ds)");
        UnheldNumber why = UnheldNumber.NO_REPRESENTATION_EXISTS;

        Classification at = InputClassifications.decided(axis, List.of("over", "under"),
                List.of(new Membership.NotWorkedOut(why), new Membership.NotWorkedOut(why)),
                new ObservedValue.Integer(0));

        assertTrue(at instanceof Classification.Unclassified,
                "a count the exact arithmetic could not work out settles no class, and is not"
                        + " read as one that definitely holds none either");
        assertEquals(Incompleteness.Code.VALUE_NOT_WORKED_OUT,
                ((Classification.Unclassified) at).reason().code(),
                "the coverage word for this is its own, not an observation code and not silence");
    }
}
