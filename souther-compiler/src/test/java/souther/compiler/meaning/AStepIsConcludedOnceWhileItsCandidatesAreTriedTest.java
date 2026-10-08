package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.semantics.ConditionJoin;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * While the candidates for each expression of a condition are tried, a step is concluded once.
 *
 * <p>A candidate for an expression holds the derivations of the parts under it, and those were
 * concluded when the parts were chosen. Concluded again for every expression they stand under, a
 * condition as deep as the source allows is concluded as many times over as it is deep; so what the
 * candidates are asked comes from a concluding that keeps what each step came to
 * ({@link Conclusion#reusing}). The concluding of the derivation kept is a fresh one, since the
 * parts nothing read are numbered there.
 */
class AStepIsConcludedOnceWhileItsCandidatesAreTriedTest {

    private static final Derivation PART =
            new Derivation.ATruthAtAPosition(TermPath.of("a"), true);

    private static final Derivation WHOLE = new Derivation.Joined(ConditionJoin.BOTH, PART,
            new Derivation.ATruthAtAPosition(TermPath.of("b"), true));

    @Test
    void aStepAlreadyConcludedIsNotConcludedAgain() {
        Conclusion trying = Conclusion.reusing();
        Proposition part = trying.of(PART);
        trying.of(WHOLE);
        assertSame(part, trying.of(PART),
                "the part, concluded when it was chosen, is what the whole was concluded over");
        assertSame(part, trying.concludedAt(PART));
    }

    /** And it states what a fresh concluding states. */
    @Test
    void whatItStatesIsWhatAFreshConcludingStates() {
        Conclusion trying = Conclusion.reusing();
        trying.of(PART);
        assertEquals(new Conclusion(Optional.empty()).of(WHOLE), trying.of(WHOLE));
    }

    /** A concluding of a condition is not one of these: each step is concluded where it is met. */
    @Test
    void theConcludingOfAConditionConcludesWhatItIsAskedOf() {
        Conclusion numbering = new Conclusion(Optional.empty());
        Proposition part = numbering.of(PART);
        assertNotSame(part, numbering.of(PART));
    }
}
