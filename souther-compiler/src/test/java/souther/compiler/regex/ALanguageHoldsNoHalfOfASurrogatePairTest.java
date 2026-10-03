package souther.compiler.regex;

import java.util.List;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A language this compiler answers about holds no text with half of a surrogate pair in it, so a
 * question asked of the strings a position admits is never answered by text no {@code String} is.
 *
 * <p>The machines are the shared reader's and hold no such half; what is asked here is that the
 * languages built on them keep that, the ones made out of everything else — a complement, the
 * language of every string — included.
 */
class ALanguageHoldsNoHalfOfASurrogatePairTest {

    @Test
    void noLanguageHoldsHalfAPair() {
        String high = String.valueOf((char) 0xD800);
        String low = String.valueOf((char) 0xDC00);
        for (String pattern : List.of(".", "[\\s\\S]*", "[^a]*", ".{1,2}")) {
            Language language = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                    PatternParser.read(pattern)).meaning())
                    .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
            for (String text : List.of(high, low, low + high, "a" + high)) {
                assertFalse(language.has(text), pattern);
            }
            assertFalse(language.not(PatternPlan.Budget.OF_ADMITTED_VALUES.meter()).has(high),
                    "nor does what " + pattern + " leaves out");
        }
        assertFalse(Language.EVERY_STRING.has(high));
    }
}
