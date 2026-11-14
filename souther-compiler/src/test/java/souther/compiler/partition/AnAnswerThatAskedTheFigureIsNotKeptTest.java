package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AffineForms;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.Type;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading that asked the figure counting elements anything, whether it answered or refused, is
 * the answer of the figure's state then, and is not kept for a reading that may find it otherwise.
 *
 * <p>The count of what was read does not say it: a refusal adds nothing to it, and what follows a
 * refusal is another rule that may come to a form.
 */
class AnAnswerThatAskedTheFigureIsNotKeptTest {

    private static final SourcePos NOWHERE = new SourcePos(0, 0);

    private static final AffineForms.Outcome<Object, String> A_FORM =
            new AffineForms.Outcome.Composed<>(LinearForm.constant(ExactRatio.of(1)));

    private static final AffineForms.Outcome<Object, String> A_PLAIN_STOP =
            new AffineForms.Outcome.StoppedAt<>(new Core.Int(0, Type.INT, NOWHERE), "here",
                    new AffineForms.Halt.NoRule<>());

    private static final AffineForms.Outcome<Object, String> A_STOP_AT_A_FIGURE =
            new AffineForms.Outcome.StoppedAt<>(new Core.Int(0, Type.INT, NOWHERE), "here",
                    new AffineForms.Halt.DeclinedAtAFigure<>(WhyUnread.PAST_THE_TOTAL_READINGS));

    @Test
    void anAnswerThatLeftTheFigureAloneIsKeptWhetherItIsAFormOrAStop() {
        assertTrue(KeptAnswers.keepable(true, 3, 3, A_FORM));
        assertTrue(KeptAnswers.keepable(true, 3, 3, A_PLAIN_STOP));
    }

    @Test
    void anAnswerThatAskedTheFigureIsNotKeptWhateverItCameTo() {
        for (Object answer : new Object[] {A_FORM, A_PLAIN_STOP, A_STOP_AT_A_FIGURE}) {
            assertFalse(KeptAnswers.keepable(true, 3, 4, answer), "asked once: " + answer);
            assertFalse(KeptAnswers.keepable(true, 3, 7, answer), "asked often: " + answer);
        }
    }

    @Test
    void anAnswerThatChargedWhatIsLeftOrStoppedAtAFigureIsNotKept() {
        assertFalse(KeptAnswers.keepable(false, 3, 3, A_FORM));
        assertFalse(KeptAnswers.keepable(true, 3, 3, A_STOP_AT_A_FIGURE));
    }

    /** What the rule above is told by: asked of whether it answers or refuses. */
    @Test
    void theFigureIsCountedAskedOfWhetherItAnswersOrRefuses() {
        AffineReading.WhatWasTold told = new AffineReading.WhatWasTold();
        assertEquals(0, told.askedOfTheFigure());

        Optional<WhyUnread> answered = told.declinedAtCounting(1);
        assertTrue(answered.isEmpty());
        assertEquals(1, told.askedOfTheFigure());

        Optional<WhyUnread> refused = told.declinedAtCounting(Integer.MAX_VALUE / 2);
        assertTrue(refused.isPresent(), "a list past the figure is refused");
        assertEquals(2, told.askedOfTheFigure(), "a refusal is an ask as well");

        assertEquals(3, askedAfter(told.apart(), 1), "a part read apart counts with its whole");
        assertEquals(3, told.askedOfTheFigure());
    }

    private static int askedAfter(AffineReading.WhatWasTold apart, int elements) {
        apart.declinedAtCounting(elements);
        return apart.askedOfTheFigure();
    }
}
