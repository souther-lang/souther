package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Composing a value writes none of its text: the text of each level is put together where it is
 * asked for, once for the whole ({@link FixtureText}).
 */
class AFixturesTextIsPutTogetherWhenItIsAskedForTest {

    /** Each level holds the one below it twice, so the text of the whole is longer than any host
     *  holds and composing it is as many steps as there are levels. */
    @Test
    void aValueWhoseTextNoHostHoldsIsComposed() {
        FixtureTemplate nested = FixtureTemplate.integer(1);
        for (int level = 0; level < 100; level++) {
            nested = FixtureTemplate.collection(List.of(nested, nested));
        }

        assertNotEquals(null, nested.value());
    }

    @Test
    void theTextIsTheSameHoweverItWasPutTogether() {
        FixtureText inner = FixtureText.around("[", List.of(FixtureText.word("1"),
                FixtureText.word("2")), "]");
        FixtureText outer = FixtureText.around("A { xs = ", List.of(inner, FixtureText.word("n")),
                " }");

        assertEquals("[1, 2]", inner.written());
        assertEquals("A { xs = [1, 2], n }", outer.written());
        assertEquals(outer.written(), outer.written());
        assertEquals(FixtureText.word("[1, 2]"), inner);
        assertEquals(FixtureText.word("[1, 2]").hashCode(), inner.hashCode());
        assertEquals("[]", FixtureText.around("[", List.of(), "]").written());
    }
}
