package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.runtime.Strings;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A conversion ends a run where its answer is longer than a {@code String} holds, and the answer is
 * longer than the string only where the string holds a code point answered with several. So the
 * strings a relation after it is open for are those holding one, and only at the lengths past what
 * every string is gotten past at; a string of any other code points is gotten past at every
 * length, and a string no longer than that is gotten past whatever it holds.
 */
class TheStringsAConversionMayStopOnAreOpenAtTheLengthsItMayAndNowhereElseTest {

    private static String lengthAndEquality(String conversion, String type) {
        return """
                module b1

                data S = String
                    invariant %s

                behavior f : (email: S, emails: List<S>) -> Int
                let f (email, emails) =
                    String.length(%s(email.value))
                        + List.length(List.filter(own -> own.value == email.value, emails))

                example f
                    | "match" : (S("ab"), [ S("ab") ]) -> 3
                    | "none" : (S("ab"), [ S("cd") ]) -> 2
                """.formatted(type, conversion);
    }

    private static final String ANY_STRING = "String.length(value) >= 0";

    /** Any string may hold a code point the lowercase answers with two, so the strings past what it
     *  is gotten past at every string are open, and they are all that is. */
    @Test
    void onlyTheStringsPastTheLengthEveryStringIsGottenPastAtAreOpenForTheLowercase() {
        Map<String, List<BlockReason.RelationShownOverARegion>> open =
                WhereAStringRelationIsLeftOpen.leftOpen(
                        lengthAndEquality("String.lowercase", ANY_STRING), "f");

        assertEquals(List.of("email", "emails[*]"), List.copyOf(open.keySet()));
        open.values().forEach(each -> {
            BlockReason.RelationShownOverARegion region = each.getFirst();
            assertEquals(List.of("String.lowercase"), region.notShownGottenPast());
            assertEquals(List.of(), region.imagesNotShown());
            assertTrue(!region.atAnyLength() && region.shorterThan() == null
                    && region.longerThan() > 0 && region.longerThan() < Strings.LONGEST_TEXT,
                    region::toString);
        });
    }

    /** The strings are held to a length no conversion lengthens one past. */
    @Test
    void aStringHeldToALengthTheConversionIsGottenPastAtEveryStringIsRead() {
        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(
                lengthAndEquality("String.lowercase", "String.length(value) <= 254"), "f"));
    }

    /** The code points the strings hold are answered with one, whatever stands beside them. */
    @Test
    void aStringOfCodePointsTheConversionAnswersWithOneIsReadAtEveryLength() {
        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(
                lengthAndEquality("String.lowercase", "String.matches(\"[a-z@.]+\", value)"), "f"));
        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(
                lengthAndEquality("String.uppercase", "String.matches(\"[a-z@.]+\", value)"), "f"));
    }

    /** A sharp s is answered with two by the uppercase and with one by the lowercase. */
    @Test
    void theCodePointsAConversionLengthensAreThoseItAnswersWithSeveral() {
        String sharp = "String.matches(\"[a-zß]+\", value)";

        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(
                lengthAndEquality("String.lowercase", sharp), "f"));
        assertEquals(List.of("email", "emails[*]"), List.copyOf(
                WhereAStringRelationIsLeftOpen.leftOpen(
                        lengthAndEquality("String.uppercase", sharp), "f").keySet()));
    }
}
