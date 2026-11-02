package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A string held equal to what a case conversion makes of a string is read through the
 * conversion: a string of the first side is the other's where some string of the other converts
 * to it, which is a statement about the two languages and not about the strings at one place.
 * Where every string the stored side admits is some string's lowercase, the stored side is all
 * reached and no class parts it; where it admits an uppercase letter, the strings that have one
 * are never the lowercase of a string, and the stored side is parted.
 */
class AStoredStringEqualToTheLowercaseOfAStringIsReadTest {

    private static final String DECLARATIONS = """
            module demo

            data Domain = String
                invariant String.matches("PATTERN", value)

            behavior f : (own: Domain, s: String) -> Bool
            let f (own, s) = BODY
            """;

    private static String report(String pattern, String body) {
        Compilation compilation = Compilation.ofSource(
                DECLARATIONS.replace("PATTERN", pattern).replace("BODY", body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static final List<String> BODIES = List.of("own.value == String.lowercase(s)",
            "String.lowercase(s) == own.value", "own.value /= String.lowercase(s)",
            "String.lowercase(s) /= own.value");

    @Test
    void aStoredStringOfLowercaseLettersIsReachedByTheLowercaseOfAString() {
        for (String body : BODIES) {
            String json = report("[a-z0-9.]+", body);
            assertTrue(json.contains("relation_shown_over_a_region"), () -> body + " " + json);
            assertFalse(json.contains("relation_not_shown_to_reach_every_value"),
                    () -> body + " " + json);
            assertFalse(json.contains("is never String.lowercase(s)"), () -> body + " " + json);
        }
    }

    /** An order between the two is no equality of what the conversion makes, and is not read as
     *  one. */
    @Test
    void anOrderAgainstTheLowercaseIsNotReadThroughTheConversion() {
        for (String body : List.of("own.value < String.lowercase(s)",
                "String.lowercase(s) <= own.value")) {
            String json = report("[a-z0-9.]+", body);
            assertTrue(json.contains("relation_not_shown_to_reach_every_value"),
                    () -> body + " " + json);
            assertFalse(json.contains("relation_shown_over_a_region"), () -> body + " " + json);
        }
    }

    /** A string against its own lowercase is made of one position, which no two texts are. */
    @Test
    void aStringAgainstItsOwnLowercaseIsNotReadAsTwoTexts() {
        String json = report("[a-z0-9.]+", "own.value == String.lowercase(own.value)");
        assertFalse(json.contains("relation_shown_over_a_region"), json);
        assertFalse(json.contains("can be String.lowercase"), json);
    }

    /**
     * The other side is called what it is, the lowercase of {@code s}: a stored string that
     * matches it need not be {@code s}, and no string of {@code s} is the stored one.
     */
    @Test
    void theOtherSideIsNamedByWhatItIsMadeOf() {
        for (String body : BODIES) {
            String json = report("[A-Za-z0-9.]+", body);
            assertTrue(json.contains("own: x can be String.lowercase(s)")
                    && json.contains("own: x is never String.lowercase(s)"),
                    () -> body + " " + json);
            assertFalse(json.contains("own: x can be s\"") || json.contains("own: x is never s\""),
                    () -> body + " " + json);
        }
    }

    /**
     * A string whose lowercase is no string of its own code points is not shown to be a lowercase
     * of anything: the stored side that admits one is not all reached, and the conversion is named
     * as an image not shown.
     */
    @Test
    void aStoredStringThatNoMapOfCodePointsReachesIsNotShownReached() {
        for (String pattern : List.of("[a-zİ]+", "[a-zΣ]+", "[a-zẞ]+")) {
            String json = report(pattern, "own.value == String.lowercase(s)");
            assertTrue(json.contains("\"imagesNotShown\" : [ \"String.lowercase\" ]"),
                    () -> pattern + " " + json);
            assertTrue(json.contains("own: x is never String.lowercase(s)"),
                    () -> pattern + " " + json);
        }
    }

    @Test
    void aStoredStringThatMayHaveUppercaseLettersIsPartedFromTheOnesNoLowercaseIs() {
        for (String body : BODIES) {
            String json = report("[A-Za-z0-9.]+", body);
            assertFalse(json.contains("relation_not_shown_to_reach_every_value"),
                    () -> body + " " + json);
            assertTrue(json.contains("own: x can be String.lowercase(s)")
                    && json.contains("own: x is never String.lowercase(s)"),
                    () -> body + " " + json);
        }
    }
}
