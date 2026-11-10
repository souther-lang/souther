package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comment written after code on the same line comes back on that code's line, and it is not
 * content the layout has to make room for.
 *
 * <p>Which code a comment is about, in every way a member can be written, is
 * {@link ACommentKeepsItsMemberHoweverItIsWrittenTest}'s. What is asked here is the other half: the
 * layout is re-derived, so where a construct ends is a derived value, and a comment at the end of
 * its line sits past that end whatever its length. Measuring the line against it would break a
 * construct that fits, and a construct that does break still breaks on its own width.
 */
class ACommentAtTheEndOfALineStaysOnItTest {

    /** The source with every comment taken off the end of its line. */
    private static String withoutComments(String text) {
        return String.join("\n", List.of(text.split("\n", -1)).stream()
                .map(line -> line.replaceAll("\\s*//.*$", "")).toList());
    }

    /**
     * The layout of a source is the layout it has without its comments, and the comments come back
     * after the code they were written after: a construct that fits is not broken for one, and one
     * that does not fit is broken as it would be without.
     */
    @Test
    void aCommentAtTheEndOfALineAddsNothingToTheLayout() {
        List<String> sources = List.of("""
                module m
                data WebForm
                data PhoneInquiry
                data Inbound = WebForm | PhoneInquiry   // a comment long enough that the line it is written on runs well past the hundred columns the canonical form is measured against
                """, """
                module m
                data AlphaMeasurement
                data BetaMeasurement
                data GammaMeasurement
                data DeltaMeasurement
                data EpsilonMeasurement
                data Measurement = AlphaMeasurement | BetaMeasurement | GammaMeasurement | DeltaMeasurement | EpsilonMeasurement   // five of them
                """);
        for (String source : sources) {
            String formatted = Formatter.format(source);

            assertEquals(Formatter.format(withoutComments(source)), withoutComments(formatted),
                    "the same layout with the comment as without it");
            assertEquals(1, formatted.lines().filter(line -> line.contains("//")).count());
        }
    }
}
