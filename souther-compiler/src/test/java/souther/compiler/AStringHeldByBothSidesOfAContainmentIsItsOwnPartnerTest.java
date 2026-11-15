package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A string that both sides of a containment hold, with the same conversion done to both, stands
 * inside its own answer: the string a side holds is among the strings the other can hold, whatever
 * the conversion is exact on. So a containment of two converted strings is read over every string,
 * and what a run that gets past the conversion cannot reach is all that is left open.
 */
class AStringHeldByBothSidesOfAContainmentIsItsOwnPartnerTest {

    private static final String SHORT = """
            data Short = String
                invariant String.length(value) <= 200
            """;

    private static Map<String, List<BlockReason.RelationShownOverARegion>> open(
            String type, String text, String declarations) {
        return WhereAStringRelationIsLeftOpen.leftOpen("""
                module d6

                %s
                behavior f : (p: %s, bc: %s) -> Bool

                let f (p, bc) = String.contains(%s, %s)
                """.formatted(declarations, type, type,
                text.formatted("p"), text.formatted("bc")), "f");
    }

    @Test
    void aContainmentOfTwoLowercasedBoundedStringsIsReadOverEveryString() {
        assertEquals(Map.of(), open("Short", "String.lowercase(%s.value)", SHORT));
    }

    /** However long the strings are: where the lowercase stops a run is where a {@code String}
     *  stops, which no value is open for, as none is where neither string is converted. */
    @Test
    void aContainmentOfTwoLowercasedStringsOfAnyLengthLeavesNoStringOpen() {
        assertEquals(Map.of(), open("String", "String.lowercase(%s)", ""));
    }

    /**
     * A string looked for that is a value is inside the value it makes with stable starters after
     * it, so the string looked for is open nowhere where the one looked in is held only to a
     * length. The short strings of the one looked in are the guard's, which keeps them from the
     * relation, and are none the relation is asked of.
     */
    @Test
    void aStringLookedForIsInsideWhatItMakesWithStarterAfterItWhereTheOtherIsHeldToALength() {
        Map<String, List<BlockReason.RelationShownOverARegion>> open =
                WhereAStringRelationIsLeftOpen.leftOpen("""
                        module e2

                        behavior f : (a: String, b: String) -> Int
                        let f (a, b) = {
                            guard String.length(a) >= 3 else 0
                            if String.contains(b, a) then 1 else 2
                        }
                        """, "f");

        assertEquals(Map.of(), open);
    }

    /**
     * The same where both are lowercased: the starters written after the string looked for are
     * ones the lowercase cuts at, so its lowercase is inside the lowercase of what they make, and
     * nothing of it is open. The short strings of the one looked in are the guard's.
     */
    @Test
    void aLowercasedStringLookedForIsInsideWhatItMakesWithStartersTheLowercaseCutsAt() {
        Map<String, List<BlockReason.RelationShownOverARegion>> open =
                WhereAStringRelationIsLeftOpen.leftOpen("""
                        module l3

                        behavior f : (a: String, b: String) -> Int
                        let f (a, b) = {
                            guard String.length(a) >= 3 else 0
                            if String.contains(String.lowercase(b), String.lowercase(a))
                            then 1 else 2
                        }
                        """, "f");

        assertEquals(Map.of(), open);
    }

    @Test
    void aContainmentOfTwoStringsWithNoConversionLeavesNoStringOpen() {
        assertEquals(Map.of(), open("String", "%s", ""));
    }
}
