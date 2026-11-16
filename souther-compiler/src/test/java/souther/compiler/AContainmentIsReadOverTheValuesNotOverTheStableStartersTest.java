package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A string inside another is asked of the values a side holds, which are its strings in
 * Normalization Form C, and not of the part of them made of stable starters. A lone combining mark,
 * or a mark after a letter it composes with nothing, is a value and is inside others, so a model
 * whose strings hold marks is read as one whose strings hold none is.
 */
class AContainmentIsReadOverTheValuesNotOverTheStableStartersTest {

    static String contains(String alphabet) {
        return """
                module k16

                data T = String
                    invariant String.matches("%s", value) && String.length(value) <= 5

                behavior f : (p: T, bc: T) -> Bool
                let f (p, bc) = String.contains(p.value, bc.value)
                """.formatted(alphabet);
    }

    /**
     * A combining mark, which composes with the letter before it and is no stable starter. The
     * other kinds of code point that are none are asked at night
     * ({@link EveryKindOfCodePointThatIsNoStableStarterIsReadInAContainmentTest}).
     */
    @Test
    void aStringOverLettersAndCombiningMarksIsReadAtBothSides() {
        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(
                contains("[a-z\\\\u0300-\\\\u036F]+"), "f"));
    }
}
