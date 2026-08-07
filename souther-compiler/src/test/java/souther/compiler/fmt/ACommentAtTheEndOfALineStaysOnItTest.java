package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comment written after code on the same line was written about that code, and it comes back on
 * that code's line. It used to be handed to whatever was declared next, which is a different claim
 * about the same words and one a reader has no way to see was ever made.
 *
 * <p>The line it comes back on is the line the code ends on after formatting, which is not
 * necessarily the line it ended on before: the layout is re-derived, so where a construct ends is a
 * derived value and only which construct the comment is about is preserved.
 */
class ACommentAtTheEndOfALineStaysOnItTest {

    @Test
    void onTheDeclarationItWasWrittenAfter() {
        String formatted = Formatter.format("""
                module m
                data WebForm
                data PhoneInquiry
                data Inbound = WebForm | PhoneInquiry      // three units; nothing to attribute
                data LeadSource = Inbound
                """);

        assertEquals("""
                module m

                data WebForm

                data PhoneInquiry

                data Inbound = WebForm | PhoneInquiry // three units; nothing to attribute

                data LeadSource = Inbound
                """, formatted);
    }

    /** A trailing comment is not content the width has to make room for. It sits past the end of the
     * line whatever its length, so measuring the line against it would break a construct that fits. */
    @Test
    void andDoesNotCountTowardsTheWidth() {
        String formatted = Formatter.format("""
                module m
                data WebForm
                data PhoneInquiry
                data Inbound = WebForm | PhoneInquiry   // a comment long enough that the line it is written on runs well past the hundred columns the canonical form is measured against
                """);

        assertEquals("""
                module m

                data WebForm

                data PhoneInquiry

                data Inbound = WebForm | PhoneInquiry // a comment long enough that the line it is written on runs well past the hundred columns the canonical form is measured against
                """, formatted);
    }

    /** The declaration's own layout still comes from its own width. */
    @Test
    void whileTheDeclarationItselfStillBreaksOnIts() {
        String formatted = Formatter.format("""
                module m
                data AlphaMeasurement
                data BetaMeasurement
                data GammaMeasurement
                data DeltaMeasurement
                data EpsilonMeasurement
                data Measurement = AlphaMeasurement | BetaMeasurement | GammaMeasurement | DeltaMeasurement | EpsilonMeasurement   // five of them
                """);

        assertEquals("""
                module m

                data AlphaMeasurement

                data BetaMeasurement

                data GammaMeasurement

                data DeltaMeasurement

                data EpsilonMeasurement

                data Measurement = AlphaMeasurement
                    | BetaMeasurement
                    | GammaMeasurement
                    | DeltaMeasurement
                    | EpsilonMeasurement // five of them
                """, formatted);
    }
}
