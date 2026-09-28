package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

import souther.compiler.inputs.Membership;
import souther.compiler.numeric.Count;
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
        Count from = Count.of(1);
        // A decimal a model can write, so far above `from` that their exact difference is a whole
        // number with more digits than any whole number the host holds — which is what stands for
        // two decimals a model wrote near opposite ends of the scale range.
        Count farBeyondWhatAWholeNumberHolds =
                Count.of(new BigDecimal(BigInteger.ONE, -2_000_000_000));
        ContainersAddingUp.Ends ends = new ContainersAddingUp.Ends(
                from, null, farBeyondWhatAWholeNumberHolds, NumericDomain.Bounds.OPEN);

        assertTrue(ends.reaches(BigDecimal.valueOf(2), 1),
                "the exact arithmetic could not hold the distance to the end, and that is never a"
                        + " proof that no arrangement reaches the total");
    }

    /**
     * {@link InputClassifications#decided} used to have no arm for {@link Membership.NotWorkedOut}
     * beyond a thrown {@code IllegalStateException}, reachable from an ordinary rule bounding a
     * count taken as a sum over a {@code List<Decimal>} spaced far enough apart in scale. It now
     * answers {@link Classification.Unclassified} carrying its own code for each of the two ways
     * {@link UnheldNumber} tells apart — a host that could still answer with more room, and no
     * representation existing at all — rather than a crash, and rather than folding the two into
     * one word once {@code UnheldNumber}'s own distinction had already been worked out.
     */
    @ParameterizedTest
    @EnumSource(UnheldNumber.class)
    void aClassAskedACountItCouldNotWorkOutIsUndeterminedRatherThanACrashOrADecidedAnswer(
            UnheldNumber why) {
        AxisId axis = new AxisId("overDecimals", "List.sum(ds)");

        Classification at = InputClassifications.decided(axis, List.of("over", "under"),
                List.of(new Membership.NotWorkedOut(why), new Membership.NotWorkedOut(why)),
                new ObservedValue.Integer(0));

        assertTrue(at instanceof Classification.Unclassified,
                "a count the exact arithmetic could not work out settles no class, and is not"
                        + " read as one that definitely holds none either");
        Incompleteness.Code expected = switch (why) {
            case NO_REPRESENTATION_EXISTS -> Incompleteness.Code.VALUE_NOT_WORKED_OUT;
            case MORE_ROOM_COULD_ANSWER -> Incompleteness.Code.VALUE_ROOM_EXCEEDED;
        };
        assertEquals(expected, ((Classification.Unclassified) at).reason().code(),
                "the coverage word keeps which of the two ways the arithmetic went unheld, the"
                        + " same distinction UnheldNumber's own contract says a reader is told");
    }
}
