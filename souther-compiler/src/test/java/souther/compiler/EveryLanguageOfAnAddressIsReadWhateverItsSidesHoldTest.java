package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.test.Nightly;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.APieceOfAConvertedStringIsReadWhateverTheRestOfTheStringHoldsTest.screen;

/**
 * Whichever side of the {@code @} holds any code point, the address is read: the four languages
 * that two sides, each any code point or letters only, make. The claim of
 * {@link APieceOfAConvertedStringIsReadWhateverTheRestOfTheStringHoldsTest}, which asks it of any
 * code point on both sides, asked of each side held to letters as well.
 *
 * <p>Deferred to the night for what it costs: a model compiled and measured for each language,
 * four of them. No cheaper way was found to know that the sides do not turn on each other, and
 * what it finds is as well found by the morning as by the change that caused it, because the
 * piece an address is cut into is read the same whichever side holds the code points.
 */
@Nightly
class EveryLanguageOfAnAddressIsReadWhateverItsSidesHoldTest {

    @Test
    void anAddressIsReadWhereverItHoldsCodePointsAConversionDoesNotMapOneToOne() {
        for (String pattern : List.of(
                "[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+",
                "[a-zA-Z0-9]+@[a-zA-Z0-9\\\\-]+\\\\.[a-zA-Z0-9.\\\\-]+",
                "[^@\\\\s]+@[a-zA-Z0-9\\\\-]+\\\\.[a-zA-Z0-9.\\\\-]+",
                "[a-z]+@[^@\\\\s]+\\\\.[^@\\\\s]+")) {
            assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen(screen(pattern),
                    "screen"), pattern);
        }
    }
}
