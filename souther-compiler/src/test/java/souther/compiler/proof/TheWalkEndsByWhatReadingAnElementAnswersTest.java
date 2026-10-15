package souther.compiler.proof;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The walk ends because reading an element answers something only below the list's length, and by
 * nothing else.
 *
 * <p>Asked of laws written here, over arguments named by their places, so what is held is the
 * proof and not the library's own law: a law that bounds the index from below only, or not at all,
 * leaves a walk that could call itself for ever, and is no proof that it ends.
 */
class TheWalkEndsByWhatReadingAnElementAnswersTest {

    private static final LawNumber<Integer> INDEX = new LawNumber.AnArgument<>(0);
    private static final LawNumber<Integer> LENGTH =
            new LawNumber.SizeOf<>(new LawSubject.Argument<>(1));

    private static OperationLaw<Integer> presentWhere(List<LawProposition<Integer>> parts) {
        LawProposition<Integer> holds = parts.size() == 1 ? parts.get(0)
                : new LawProposition.All<>(parts);
        return new OperationLaw.Observation<>(AnswerAspect.PRESENCE, holds);
    }

    /** {@code index >= 0}. */
    private static LawProposition<Integer> fromNought() {
        return new LawProposition.Compared<>(LinearForm.atom(INDEX), Rel.GE);
    }

    /** {@code length - index - 1 >= 0}. */
    private static LawProposition<Integer> belowTheLength() {
        return new LawProposition.Compared<>(new LinearForm<>(ExactRatio.of(-1),
                Map.of(LENGTH, ExactRatio.ONE, INDEX, ExactRatio.of(-1))), Rel.GE);
    }

    @Test
    void aReadingThatAnswersOnlyBelowTheLengthEndsTheWalk() {
        assertTrue(TheWalkEnds.proved(presentWhere(List.of(fromNought(), belowTheLength())),
                0, 1, Integer::intValue));
    }

    @Test
    void aReadingBoundedFromBelowAloneEndsNothing() {
        assertFalse(TheWalkEnds.proved(presentWhere(List.of(fromNought())), 0, 1,
                Integer::intValue));
    }

    /** The law read over the arguments the walk hands in the other order is no law of its walk. */
    @Test
    void aLawOverTheArgumentsTheOtherWayRoundIsNoProof() {
        assertFalse(TheWalkEnds.proved(presentWhere(List.of(fromNought(), belowTheLength())),
                1, 0, Integer::intValue));
    }

    @Test
    void aLawOfAnotherSideIsNoProof() {
        assertFalse(TheWalkEnds.proved(new OperationLaw.Observation<>(AnswerAspect.EMPTINESS,
                belowTheLength()), 0, 1, Integer::intValue));
    }
}
