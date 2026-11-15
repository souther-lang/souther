package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A string inside another is asked of the values a side holds, which are its strings in
 * Normalization Form C, and not of the part of them made of stable starters. A lone combining mark,
 * or a mark after a letter it composes with nothing, is a value and is inside others, so a model
 * whose strings hold marks is read as one whose strings hold none is.
 */
class AContainmentIsReadOverTheValuesNotOverTheStableStartersTest {

    private static String contains(String alphabet) {
        return """
                module k16

                data T = String
                    invariant String.matches("%s", value) && String.length(value) <= 100

                behavior f : (p: T, bc: T) -> Bool
                let f (p, bc) = String.contains(p.value, bc.value)

                example f
                    | "in" : (T("ab"), T("xxabyy")) -> true
                    | "out" : (T("ab"), T("xxyy")) -> false
                """.formatted(alphabet);
    }

    @Test
    void aStringOverLettersAndCodePointsThatAreNoStableStarterIsReadAtBothSides() {
        for (String alphabet : List.of(
                "[a-z\\\\u0300]+",
                "[a-z\\\\u0300-\\\\u036F]+",
                "[a-z\\\\u1100-\\\\u11FF]+",
                "[a-z\\\\u0370-\\\\u03FF]+",
                "[a-z\\\\u0400-\\\\u04FF]+")) {
            assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(contains(alphabet), "f"),
                    alphabet);
        }
    }
}
