package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What a step concludes is a function of the step and of what is supposed of the values a walk
 * carried, so what a concluding says it concluded for a step is what it concluded under its own
 * supposition — whichever concluding under another one was the last to conclude it.
 */
class WhatAStepConcludedUnderASuppositionIsAskedUnderThatSuppositionTest {

    private static final ACarriedValue CARRIED = ACarriedValue.made();

    private static final Derivation STEP = new Derivation.WhatAWalkCarried(CARRIED);

    @Test
    void aStepConcludedAgainFromWhatWasKeptIsWhatItWasLastConcludedAs() {
        Conclusion yes = new Conclusion(Optional.empty()).supposing(CARRIED, true);
        Conclusion reusing = Conclusion.reusing();
        Conclusion yesHere = reusing.supposing(CARRIED, true);
        Conclusion noHere = reusing.supposing(CARRIED, false);

        Proposition expected = yesHere.of(STEP);
        Proposition other = noHere.of(STEP);
        assertNotEquals(expected, other, "the two suppositions say different things");
        assertSame(expected, yesHere.of(STEP));
        assertSame(expected, yesHere.concludedAt(STEP));
        assertEquals(yes.of(STEP), yesHere.concludedAt(STEP));
    }

    @Test
    void whatAnotherSuppositionConcludedIsNotWhatThisOneConcluded() {
        Conclusion conclusion = new Conclusion(Optional.empty());
        Conclusion yes = conclusion.supposing(CARRIED, true);
        Conclusion no = conclusion.supposing(CARRIED, false);

        Proposition ofYes = yes.of(STEP);
        Proposition ofNo = no.of(STEP);
        assertNotEquals(ofYes, ofNo);
        assertSame(ofNo, no.concludedAt(STEP));
        assertSame(ofYes, yes.concludedAt(STEP),
                "no concluded the step last, and yes is not told what no concluded");
    }

    @Test
    void aStepNoConcludingUnderThisSuppositionConcludedIsNoneYet() {
        Conclusion conclusion = new Conclusion(Optional.empty());
        conclusion.supposing(CARRIED, false).of(STEP);
        assertNull(conclusion.supposing(CARRIED, true).concludedAt(STEP));
    }

    @Test
    void aReusingConcludingTellsEachSuppositionItsOwn() {
        Conclusion reusing = Conclusion.reusing();
        Conclusion yes = reusing.supposing(CARRIED, true);
        Conclusion no = reusing.supposing(CARRIED, false);

        Proposition ofYes = yes.of(STEP);
        Proposition ofNo = no.of(STEP);
        assertSame(ofYes, yes.concludedAt(STEP));
        assertSame(ofNo, no.concludedAt(STEP));
    }
}
