package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.partition.UndividedByARelation.WholeEnds;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Choosing the pivot for statements that move the form {@code p} by a number the run chooses is
 * shown only where it is shown at every number the claim speaks for
 * ({@link RemainderCoverage#proveJointly}). Each case but the first is one where the claim is
 * false at some number, so that nothing is shown; working the claim out over every row is
 * {@code AJointCoverageHoldsWhenEveryRowIsTriedTest}.
 */
class AJointProofAsksEveryNumberItSpeaksForTest {

    private static final NumericTerm P = new NumericTerm.ValueOf(TermPath.of("p"));

    /** One remainder of the form moved by the number, at every number from nought to five, inside
     *  a type wide enough for every value of the pivot. */
    @Test
    void aClaimThatHoldsAtEveryNumberIsShown() {
        assertTrue(proveJointly(ends(-10, 10), 1, List.of(moved(0, 1, 0)), List.of(), 2,
                ends(-100, 100), 0, 5).isPresent());
    }

    /** Moved by three and twice the number, the form is past the type's upper end of fifteen for
     *  every value of the pivot from the number seven on: the claim fails there, and what is
     *  shown at the numbers before shows nothing of those. */
    @Test
    void aNumberTheClaimFailsAtLeavesNothingShown() {
        assertTrue(proveJointly(ends(0, 2), 1, List.of(moved(3, 2, 1)), List.of(), 2,
                ends(-29, 15), 3, 11).isEmpty());
    }

    /** The numbers from three to fourteen are more than twice the divisor, so the proof asks the
     *  first three and the last three, every remainder the number leaves at each end. Twelve and
     *  thirteen leave no value of the pivot inside the type, and fourteen is no number the claim
     *  speaks for, since its remainder is one the number's own statement does not allow: asked at
     *  the two ends alone, the upper end asks nothing. */
    @Test
    void everyRemainderOfTheNumberIsAskedAtEachEnd() {
        assertTrue(proveJointly(ends(-1, 1), 1, List.of(moved(2, 2, 1, 2)),
                List.of(moved(0, 1, 0, 1)), 3, ends(-30, 24), 3, 14).isEmpty());
    }

    /** At the one number, the first statement allows the form only at the remainder three and the
     *  second only at one or two, so no one remainder meets them both. */
    @Test
    void statementsNoRemainderOfTheFormMeetsTogetherLeaveNothingShown() {
        assertTrue(proveJointly(ends(-1, 2), -1, List.of(moved(3, 0, 2), moved(-2, -1, 0, 3)),
                List.of(), 4, ends(-26, 16), 0, 0).isEmpty());
    }

    private static Optional<RemainderCoverage.Proof> proveJointly(
            WholeEnds pivotEnds, int onPivot, List<RemainderCoverage.Moved> statements,
            List<RemainderCoverage.Moved> ofTheNumber, int divisor, WholeEnds type, long low,
            long high) {
        return RemainderCoverage.proveJointly(P, pivotEnds, Map.of(),
                new LinearForm<>(ExactRatio.ZERO, Map.of(P, ExactRatio.of(onPivot))), statements,
                ofTheNumber, BigInteger.valueOf(divisor), List.of(), type.low(), type.high(), low,
                high);
    }

    /** A statement moving the form by {@code shift} and {@code onTheNumber} times the number, and
     *  allowing the remainders {@code allowed}. */
    private static RemainderCoverage.Moved moved(int shift, int onTheNumber,
                                                 Integer... allowed) {
        return new RemainderCoverage.Moved(BigInteger.valueOf(shift),
                BigInteger.valueOf(onTheNumber), Set.of(allowed));
    }

    private static WholeEnds ends(int low, int high) {
        return new WholeEnds(BigInteger.valueOf(low), BigInteger.valueOf(high));
    }
}
