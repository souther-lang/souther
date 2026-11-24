package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a run taking an arm works out, kept by a candidate for each comparison the arm was read
 * as, is held by the candidate that tried it when that one's rule is kept: for a comparison read
 * as a relation, and for one read as cutting nothing, which draws none.
 */
class AnAbsorbedCandidateKeepsEveryComparisonItsArmsWereReadAsTest {

    @Test
    void whatItKeptOfEachKindOfComparisonIsHeldByTheOneThatAbsorbedIt() {
        Relation relation = new Relation.Affine(LinearForm.constant(ExactRatio.ZERO), Rel.GE);
        Derivation cut = new Derivation.ACutThatCutsNothing(true, Set.of());
        Derivation alike = new Derivation.ACutThatCutsNothing(true, Set.of());
        Pullback.OnThisArm arm = new Pullback.OnThisArm(() ->
                AffineReading.WorkedOut.ofWhatIsToldOf(UndividedByARelation.Working.UNREAD),
                () -> StopEvidence.ofWhatIsToldOf(UndividedByARelation.Working.AS_THE_FORM),
                List.of());
        Pullback.Trial kept = new Pullback.Trial();
        kept.readOnAnArm(new Pullback.ArmRead.OfARelation(relation), arm);
        kept.readOnAnArm(new Pullback.ArmRead.OfAComparisonThatDrawsNoLine(cut), arm);
        kept.readOnAnArm(new Pullback.ArmRead.OfTheAnswerOfAnArm(cut), arm);

        Pullback.Trial absorbing = new Pullback.Trial();
        absorbing.absorb(kept);

        assertEquals(List.of(arm), absorbing.onTheArms(new Pullback.ArmRead.OfARelation(relation)));
        assertEquals(List.of(arm),
                absorbing.onTheArms(new Pullback.ArmRead.OfAComparisonThatDrawsNoLine(cut)));
        assertEquals(List.of(arm),
                absorbing.onTheArms(new Pullback.ArmRead.OfTheAnswerOfAnArm(cut)));
        // Two arms can cut nothing alike and work different things out: a step is its own.
        assertEquals(List.of(),
                absorbing.onTheArms(new Pullback.ArmRead.OfAComparisonThatDrawsNoLine(alike)));
        assertEquals(List.of(), absorbing.onTheArms(new Pullback.ArmRead.OfTheAnswerOfAnArm(alike)));
    }
}
