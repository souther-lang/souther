package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredBounds;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.partition.UndividedByARelation.WholeEnds;

import java.math.BigInteger;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A walk over the whole numbers from one to another, both included, ends at the second where that
 * is the last number of its type: there is no number after it to step to. Each case is a walk of
 * a few numbers ending there.
 */
class AWalkOverWholeNumbersEndsAtTheLastNumberOfItsTypeTest {

    private static final Duration A_FEW_NUMBERS = Duration.ofSeconds(5);

    /** The remainders are asked at the last number a long holds as at any other: the form and the
     *  number add up to an even number with the form at one there, and two statements no form
     *  meets are asked up to it and no further. */
    @Test
    void theRemaindersOfANumberAreAskedUpToTheLastLong() {
        assertEquals(new JointResidues.Choice(1, Long.MAX_VALUE),
                assertTimeoutPreemptively(A_FEW_NUMBERS, () -> JointResidues.between(2,
                        List.of(new JointResidues.Statement(0, 1, Set.of(0))), Long.MAX_VALUE,
                        Long.MAX_VALUE)));
        List<JointResidues.Statement> neither = List.of(
                new JointResidues.Statement(0, 0, Set.of(0)),
                new JointResidues.Statement(1, 0, Set.of(0)));
        assertEquals(new JointResidues.None(), assertTimeoutPreemptively(A_FEW_NUMBERS,
                () -> JointResidues.between(2, neither, Long.MAX_VALUE - 1, Long.MAX_VALUE)));
    }

    /** A number the run chooses up to the last long is asked at each number of a range that
     *  short, and at no other. */
    @Test
    void aJointProofOverARangeEndingAtTheLastLongAsksEachOfItsNumbers() {
        NumericTerm pivot = new NumericTerm.ValueOf(TermPath.of("p"));
        RemainderCoverage.Moved moved = new RemainderCoverage.Moved(BigInteger.ZERO,
                BigInteger.ZERO, Set.of(0));
        assertTimeoutPreemptively(A_FEW_NUMBERS, () -> RemainderCoverage.proveJointly(pivot,
                new WholeEnds(BigInteger.valueOf(-10), BigInteger.valueOf(10)), Map.of(),
                new LinearForm<>(ExactRatio.ZERO, Map.of(pivot, ExactRatio.ONE)), List.of(moved),
                List.of(), BigInteger.TWO, List.of(), BigInteger.valueOf(-100),
                BigInteger.valueOf(100), Long.MAX_VALUE - 1, Long.MAX_VALUE));
    }

    /** The counts a container may hold where the rules leave it open at the top end at the
     *  largest count an int holds. */
    @Test
    void theCountsAContainerMayHoldEndAtTheLargestInt() {
        List<Integer> counts = new ArrayList<>();
        assertTimeoutPreemptively(A_FEW_NUMBERS, () -> {
            for (int each : ContainersAddingUp.countsAdmitted(new DeclaredBounds.CountRange(
                    Integer.MAX_VALUE - 1, Integer.MAX_VALUE), null)) {
                counts.add(each);
                if (counts.size() > 2) {
                    break;
                }
            }
        });
        assertEquals(List.of(Integer.MAX_VALUE - 1, Integer.MAX_VALUE), counts);
    }
}
