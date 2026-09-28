package souther.compiler.query;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.DecidedBy;
import souther.compiler.coverage.Numberings;
import souther.compiler.partition.ClassOfAPosition;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * {@code RowWork} is a {@link Adequacy.RowsOwed} answer, and {@link Db} tells whether one changed
 * from the last by {@code equals}. A collection that answers {@code equals} about its entries and
 * not about the order they were put in would leave a plan built from a reordered answer looking
 * unchanged to whoever depends on it — {@code arms} is a {@code List<RowWork.Arm>} rather than a
 * map keyed on the identity for exactly this reason, and this pins that it stays one.
 */
class TheOrderOfARowWorksArmsIsPartOfItsAnswerTest {

    private static final SourceConstructOrigin FORK =
            SourceConstructOrigin.written(new WrittenOwner.Body("m", "b"), 0,
                    SourceConstruct.IF);

    private static final Map<Integer, ArmProbe> PLACES = Numberings.arms(2);

    private static final RowWork.Arm ARM_A = arm(0);

    private static final RowWork.Arm ARM_B = arm(1);

    private static RowWork.Arm arm(int part) {
        CoverageSites.Obligation obligation =
                new CoverageSites.Obligation("b", FORK, part, new DecidedBy.NotSaid());
        return new RowWork.Arm(new ObligationIdentity.OfAnArm(obligation),
                new Generator.ArmOwed(PLACES.get(part)));
    }

    @Test
    void twoAnswersWithTheSameArmsInADifferentOrderAreNotTheSameAnswer() {
        RowWork inOneOrder = work(List.of(ARM_A, ARM_B));
        RowWork reversed = work(List.of(ARM_B, ARM_A));

        assertNotEquals(inOneOrder, reversed,
                () -> "the order a plan is built from is part of what this answers: "
                        + inOneOrder + " vs " + reversed);
    }

    @Test
    void twoAnswersWithTheSameArmsInTheSameOrderAreTheSameAnswer() {
        assertEquals(work(List.of(ARM_A, ARM_B)), work(List.of(ARM_A, ARM_B)));
    }

    private static RowWork work(List<RowWork.Arm> arms) {
        return new RowWork(List.<ClassOfAPosition>of(), arms, List.of(), List.of(), List.of(),
                List.of());
    }
}
