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

    /**
     * The same words in the same place in the child list, told apart by the whitespace in front of
     * them: the one below carries the newline that ended the line above it and the one beside does
     * not. Written as a pair because either half alone is satisfied by a formatter that treats every
     * comment the same way.
     */
    @Test
    void whichOfTheTwoItIsComesFromTheWhitespaceBeforeIt() {
        String beside = Formatter.format("""
                module m
                data D =
                    { a: Int   // the comment
                    , b: Int
                    }
                """);
        String below = Formatter.format("""
                module m
                data D =
                    { a: Int
                    // the comment
                    , b: Int
                    }
                """);

        assertEquals("""
                module m

                data D =
                    { a: Int // the comment
                    , b: Int
                    }
                """, beside);
        assertEquals("""
                module m

                data D =
                    { a: Int
                    // the comment
                    , b: Int
                    }
                """, below);
    }

    /** A sum's cases are identifiers rather than nodes, so a case cannot be named the way a field
     * can. The comment is held against where the identifier is instead. The last case is the
     * exception: the declaration ends where it does, and what ends on a line is what the line was
     * about. */
    @Test
    void onTheSumCaseItWasWrittenAfter() {
        String formatted = Formatter.format("""
                module m
                data A
                data B
                data C
                data S = A   // about A
                    | B
                    | C
                """);

        assertEquals("""
                module m

                data A

                data B

                data C

                data S = A // about A
                    | B
                    | C
                """, formatted);
    }

    /** A comment above an attempt's departure, and above a pipeline's stage. Both are written one to
     * a line, and neither was asked for its comments. */
    @Test
    void aboveADepartureAndAboveAStage() {
        String departures = Formatter.format("""
                module m
                data Amount = Int
                    invariant value > 0
                data O = { n: Int }
                behavior f : (n: Int) -> O | Amount constructs O, Amount
                let f (n) = {
                    guard Amount(n) as a else
                        // why this arm
                        | value -> Amount(1)
                    O { n = a.value }
                }
                """);
        String stages = Formatter.format("""
                module m exposing ( p )
                data A = { n: Int }
                data B = { n: Int }
                behavior one : (a: A) -> B constructs B
                behavior p =
                    one
                    // why this stage
                    >-> one
                """);

        assertEquals("""
                module m

                data Amount = Int
                    invariant value > 0

                data O =
                    { n: Int
                    }

                behavior f : (n: Int) -> O | Amount
                    constructs O, Amount

                let f (n) = {
                    guard Amount(n) as a else
                        // why this arm
                        | value -> Amount(1)
                    O { n = a.value }
                }
                """, departures);
        assertEquals("""
                module m exposing ( p )

                data A =
                    { n: Int
                    }

                data B =
                    { n: Int
                    }

                behavior one : (a: A) -> B
                    constructs B

                behavior p =
                    one
                    // why this stage
                    >-> one
                """, stages);
    }

    @Test
    void onTheFieldItWasWrittenAfter() {
        String formatted = Formatter.format("""
                module m
                data AccountId = String
                data DomainName = String
                data Industry
                data Account =
                    { id: AccountId
                    , domain: DomainName?         // an honest optional
                    , industry: Industry
                    }
                """);

        assertEquals("""
                module m

                data AccountId = String

                data DomainName = String

                data Industry

                data Account =
                    { id: AccountId
                    , domain: DomainName? // an honest optional
                    , industry: Industry
                    }
                """, formatted);
    }

    /** In a list whose members are separated rather than opened, the comment goes after the comma:
     * the comma is on that line too, and one written after the comment would be inside it. */
    @Test
    void afterTheCommaWhenTheMemberIsFollowedByOne() {
        String formatted = Formatter.format("""
                module m
                data O = { a: Int, b: Int }
                behavior f : (n: Int) -> O constructs O
                let f (n) = O {
                  a = n,   // the first
                  b = n
                }
                """);

        assertEquals("""
                module m

                data O =
                    { a: Int
                    , b: Int
                    }

                behavior f : (n: Int) -> O
                    constructs O

                let f (n) =
                    O {
                        a = n, // the first
                        b = n
                    }
                """, formatted);
    }

    @Test
    void onTheMatchArmItWasWrittenAfter() {
        String formatted = Formatter.format("""
                module m
                data A
                data B
                data S = A | B
                data O = { n: Int }
                behavior f : (s: S) -> O constructs O
                let f (s) = O { n = match s with
                  | A -> 1   // the first
                  | B -> 2 }
                """);

        assertEquals("""
                module m

                data A

                data B

                data S = A | B

                data O =
                    { n: Int
                    }

                behavior f : (s: S) -> O
                    constructs O

                let f (s) =
                    O {
                        n = match s with
                            | A -> 1 // the first
                            | B -> 2
                    }
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
