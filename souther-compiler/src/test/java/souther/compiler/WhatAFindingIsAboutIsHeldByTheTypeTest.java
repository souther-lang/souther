package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.InputCaseEvidence;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.OutputCaseEvidence;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The states a finding's subject may not be in, refused where the value is made.
 *
 * <p>Every one of these was reachable while what a finding is about was a {@code List<Object>} of a
 * message's arguments, and every one of them was found by a reader rather than at construction. The
 * shapes that replaced the list are what says so now, so a subject is what the type promises rather
 * than what its producer happens to be doing.
 */
class WhatAFindingIsAboutIsHeldByTheTypeTest {

    /**
     * A finding is about something, and the shape says so.
     *
     * <p>Not defensive. The reader that would find out is whichever surface first asks the subject a
     * question — the human line, a document's {@code subject}, the sentence a build prints — so a
     * finding about nothing is one that survives being made, being counted, being published, and
     * fails on whichever of the three a reader happens to be looking at.
     *
     * <p>The list this replaced refused a null element as a side effect of being copied. Saying it
     * per shape keeps what the copy was doing by accident.
     */
    @Test
    void aSubjectThatIsNotThereIsRefusedWhereTheFindingIsMade() {
        assertThrows(NullPointerException.class, () -> new About.ACaseNoRowExpects(null));
        assertThrows(NullPointerException.class, () -> new About.AClassNoRowIsIn(null));
        assertThrows(NullPointerException.class, () -> new About.APointOfABorder(null));
        assertThrows(NullPointerException.class, () -> new About.AQuestionNothingAnswered(null));
        assertThrows(NullPointerException.class, () -> new About.AnArmNoRowGoesThrough(null));
        assertThrows(NullPointerException.class,
                () -> new About.ACaseNoRowAppliesItTo(InputCaseEvidence.none(0), null));
        assertThrows(NullPointerException.class,
                () -> new About.ACaseNoRowAppliesItTo(null, null));
    }

    /**
     * Which input a piece of evidence is about, and where it sits, may not differ.
     *
     * <p>Two things say it: the order of {@code signature.inputs}, which is what the document
     * publishes as the position, and the evidence's own answer, which is what a finding names a
     * position by. They are read by different surfaces. Out of step, the document would call an
     * entry the first input while a finding made from that same entry called it the second, and
     * both surfaces would go on being right about the one they read.
     *
     * <p>The evidence carries the position so that one of them means something away from this list.
     * The price of that is that the two can be said to differ, and this is where they are said to
     * agree.
     */
    @Test
    void evidenceOutOfStepWithWhereItSitsIsRefused() {
        IllegalArgumentException e = assertThrows(IllegalArgumentException.class,
                () -> signature(List.of(InputCaseEvidence.none(1), InputCaseEvidence.none(0))));

        assertEquals("the evidence at input 0 says it is input 1", e.getMessage());
    }

    /** And in step, it is the same list. */
    @Test
    void evidenceInStepWithWhereItSitsIsKept() {
        Adequacy.SignatureEvidence signature =
                signature(List.of(InputCaseEvidence.none(0), InputCaseEvidence.none(1)));

        assertEquals(List.of(0, 1), signature.inputs().stream().map(InputCaseEvidence::at).toList());
    }

    /** A position that is not one is not a position an input can be at. */
    @Test
    void anInputAtNoPositionIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> InputCaseEvidence.none(-1));
    }

    private static Adequacy.SignatureEvidence signature(List<InputCaseEvidence> inputs) {
        return new Adequacy.SignatureEvidence(OutputCaseEvidence.none(), inputs,
                MeasurementStatus.COMPLETE, null);
    }
}
