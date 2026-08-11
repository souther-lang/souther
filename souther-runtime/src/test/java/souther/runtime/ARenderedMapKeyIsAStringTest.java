package souther.runtime;

import org.junit.jupiter.api.Test;

import java.time.LocalDate;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A boundary map's key is written as a string — that is what makes a type a key at all — so the
 * helper that rewrites the keys says so and holds the renderer to it.
 *
 * <p>The renderer reaches here as an {@code Encoder}'s {@code encode} typed to its own external
 * form, so the fact is not in its type. Held here, a renderer that writes something else fails at
 * the key it wrote; held nowhere, the object travels on and is refused later as one with a key
 * nothing can name, which says nothing about which renderer produced it.
 */
class ARenderedMapKeyIsAStringTest {

    @Test
    void keysAreRewrittenByTheRenderer() {
        Map<String, Long> out = Maps.mapKeys(Map.of("a", 1L), k -> k + "!");
        assertEquals(Map.of("a!", 1L), out);
    }

    /** The rendering a temporal key goes through: the value is not a string until the renderer has
     *  run, which is what this step is for. */
    @Test
    void aRenderedTemporalIsAStringKey() {
        Map<String, Long> out =
                Maps.mapKeys(Map.of(LocalDate.parse("2026-01-01"), 1L), Object::toString);
        assertEquals(Map.of("2026-01-01", 1L), out);
    }

    @Test
    void aRendererThatDoesNotWriteAStringFailsHere() {
        assertThrows(ClassCastException.class,
                () -> Maps.mapKeys(Map.of("a", 1L), _ -> 1L));
    }

    @Test
    void theKeyFunctionFirstFormHoldsTheSameContract() {
        assertEquals(Map.of("a!", 1L), Maps.mapKeysWith(k -> k + "!", Map.of("a", 1L)));
        assertThrows(ClassCastException.class,
                () -> Maps.mapKeysWith(_ -> 1L, Map.of("a", 1L)));
    }
}
