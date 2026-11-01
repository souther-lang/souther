package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConditionJoin;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where each relation a comparison was read as is read, down the arms of an {@code if}: one read
 * in what decides the choice is read wherever the choice is made, before either way is taken;
 * one read on an arm is read where the decision takes that arm, and one on the other where it
 * takes the other ({@link MeaningsOfABody.Meaning#relationsDownTheArmsOf}). And the relations
 * alone ({@link MeaningsOfABody.Meaning#relationsReadIn}) are those, in the same order.
 *
 * <p>So what a run working the decision out does is said of every run getting to the choice —
 * a run stopping there stops whichever way the choice would have gone — and what a run working
 * an arm out does, of runs taking it.
 */
class WhereARelationIsReadDownTheArmsOfAChoiceTest {

    private static final Quantity X = new DecisionAtom.OfTheInput(
            new NumericTerm.ValueOf(TermPath.of("x")));
    private static final Relation DECIDED = new Relation.Affine(LinearForm.atom(X), Rel.GT);
    private static final Relation THEN = new Relation.Affine(LinearForm.atom(X), Rel.GE);
    private static final Relation OTHERWISE = new Relation.Affine(LinearForm.atom(X), Rel.EQ);

    @Test
    void aRelationReadInTheDecisionIsReadBeforeEitherArm() {
        Derivation decides = new Derivation.Joined(ConditionJoin.BOTH, read(DECIDED),
                new Derivation.ATruthOfASubject(new DecisionSubject.AnInput(TermPath.of("a")),
                        true));
        Derivation choice = new Derivation.IfThenElse(decides, read(THEN), read(OTHERWISE));
        Proposition taken = decides.concludes(Optional.empty());
        assertEquals(List.of(
                        new MeaningsOfABody.Meaning.ReadOnAnArm(DECIDED, Proposition.all(List.of())),
                        new MeaningsOfABody.Meaning.ReadOnAnArm(THEN, Proposition.all(List.of(taken))),
                        new MeaningsOfABody.Meaning.ReadOnAnArm(OTHERWISE,
                                Proposition.all(List.of(taken.denied())))),
                MeaningsOfABody.Meaning.relationsDownTheArmsOf(choice));
        assertEquals(List.of(DECIDED, THEN, OTHERWISE),
                MeaningsOfABody.Meaning.relationsReadIn(choice));
    }

    /** One choice inside an arm of another is read under both arms taken, the outer first. */
    @Test
    void aRelationOnAnArmOfAnArmIsReadWhereBothAreTaken() {
        Derivation outer = new Derivation.ATruthOfASubject(
                new DecisionSubject.AnInput(TermPath.of("a")), true);
        Derivation inner = new Derivation.ATruthOfASubject(
                new DecisionSubject.AnInput(TermPath.of("b")), true);
        Derivation choice = new Derivation.IfThenElse(outer,
                new Derivation.IfThenElse(inner, read(THEN), read(OTHERWISE)), read(DECIDED));
        Proposition a = outer.concludes(Optional.empty());
        Proposition b = inner.concludes(Optional.empty());
        assertEquals(List.of(
                        new MeaningsOfABody.Meaning.ReadOnAnArm(THEN, Proposition.all(List.of(a, b))),
                        new MeaningsOfABody.Meaning.ReadOnAnArm(OTHERWISE,
                                Proposition.all(List.of(a, b.denied()))),
                        new MeaningsOfABody.Meaning.ReadOnAnArm(DECIDED,
                                Proposition.all(List.of(a.denied())))),
                MeaningsOfABody.Meaning.relationsDownTheArmsOf(choice));
    }

    private static Derivation read(Relation relation) {
        return new Derivation.AComparisonRead(Derivation.ComparisonReading.BY_A_LAW, relation,
                true, Derivation.AComparisonRead.Facing.NOTHING_WRITTEN);
    }
}
