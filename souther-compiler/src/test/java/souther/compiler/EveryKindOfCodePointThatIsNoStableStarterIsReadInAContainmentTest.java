package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.test.Nightly;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.AContainmentIsReadOverTheValuesNotOverTheStableStartersTest.contains;

/**
 * A containment is read at both sides over strings of each kind of code point that is no stable
 * starter: the claim of {@link AContainmentIsReadOverTheValuesNotOverTheStableStartersTest}, asked
 * of a combining mark, a Hangul jamo, which composes with its neighbours into a syllable, and
 * letters of Greek and of Cyrillic, which have decompositions of their own, as well.
 *
 * <p>Deferred to the night for what it costs: a model compiled and measured for each alphabet, and
 * what each is asked is the same containment. No cheaper way was found to know that the kinds
 * agree, and what it finds is as well found by the morning as by the change that caused it,
 * because the mechanism is the one the combining mark exercises on every change.
 */
@Nightly
class EveryKindOfCodePointThatIsNoStableStarterIsReadInAContainmentTest {

    @Test
    void aStringOverLettersAndCodePointsThatAreNoStableStarterIsReadAtBothSides() {
        for (String alphabet : List.of(
                "[a-z\\\\u0300]+",
                "[a-z\\\\u1100-\\\\u11FF]+",
                "[a-z\\\\u0370-\\\\u03FF]+",
                "[a-z\\\\u0400-\\\\u04FF]+")) {
            assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(contains(alphabet), "f"),
                    alphabet);
        }
    }
}
