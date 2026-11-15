package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;

import java.text.Normalizer;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A string the entry says is inside what stable starters written after it make is so: some
 * starters written after it make a string of the language, and with a conversion done to both, the
 * conversion of what they make starts with the conversion of the string. And a value of the
 * language is among them, with nothing written.
 *
 * <p>Held over every string of up to three code points of an alphabet with letters, a capital
 * sigma that the code point after it decides, a combining mark, and separators.
 */
class AStringLookedForIsInsideWhatStartersWrittenAfterItMakeTest {

    private static final Meter METER = new Meter(100_000, 10_000_000, 1_000_000_000L);

    private static final int[] ALPHABET = {'a', 'B', 0x03A3, 0x0301, '@', '1', ' '};

    private static final UnaryOperator<String> LOWER =
            AStringLookedForIsInsideWhatStartersWrittenAfterItMakeTest::lowered;

    private static String lowered(String text) {
        return Normalizer.normalize(text.toLowerCase(Locale.ROOT), Normalizer.Form.NFC);
    }

    private static Language language(String regex) {
        Language made = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning()).compile(METER);
        assertNotNull(made, regex);
        return made;
    }

    private static List<String> everyString(int most) {
        List<String> all = new ArrayList<>(List.of(""));
        List<String> last = List.of("");
        for (int length = 1; length <= most; length++) {
            List<String> next = new ArrayList<>();
            for (String shorter : last) {
                for (int each : ALPHABET) {
                    next.add(shorter + Character.toString(each));
                }
            }
            all.addAll(next);
            last = next;
        }
        return all;
    }

    /** Whether some starters of the alphabet written after {@code string} make one of
     *  {@code language} whose conversion starts with the conversion of {@code string}. */
    private static boolean madeInto(String string, Language language, UnaryOperator<String> through,
                                    List<String> pads) {
        for (String pad : pads) {
            if (pad.codePoints().anyMatch(each -> Normalization.combiningClass(each) != 0)) {
                continue;
            }
            String made = string + pad;
            if (language.has(made) && through.apply(made).startsWith(through.apply(string))) {
                return true;
            }
        }
        return false;
    }

    @Test
    void whatIsSaidToBeInsideIsInsideWhatStartersWrittenAfterItMake() {
        List<String> strings = everyString(3);
        Language atLeastThree = language("[aB\\x{3A3}\\x{301}@1 ]{3,}");
        ConversionAnswers lower = ConversionAnswers.of(CodeMap.of(LOWER), LOWER);
        for (ConversionAnswers through : new ConversionAnswers[] {null, lower}) {
            UnaryOperator<String> run = through == null ? UnaryOperator.identity() : LOWER;
            Language extended = StringsInsideStrings.extendedByStableStarters(atLeastThree,
                    through, METER);
            assertNotNull(extended);
            for (String each : strings) {
                if (Normalization.nfc(each).equals(each) && extended.has(each)) {
                    assertTrue(madeInto(each, atLeastThree, run, strings),
                            () -> (through == null ? "" : "lowercased ") + named(each));
                }
            }
            assertTrue(extended.has("a"), "a string short of the length is made long enough");
        }
    }

    /** A capital sigma closes a word where nothing cased follows it, so the lowercase does not cut
     *  at a letter: a string ending in one is made long only with what is no letter. */
    @Test
    void aConversionThatTurnsOnWhatFollowsIsWrittenOnlyWhatItCutsAt() {
        Language lettersOnly = language("[aB\\x{3A3}]{3,}");
        ConversionAnswers lower = ConversionAnswers.of(CodeMap.of(LOWER), LOWER);

        assertTrue(StringsInsideStrings.extendedByStableStarters(lettersOnly, null, METER)
                .has("Σ"));
        assertFalse(StringsInsideStrings.extendedByStableStarters(lettersOnly, lower, METER)
                .has("Σ"));
    }

    private static String named(String text) {
        return text.codePoints().mapToObj(cp -> String.format("U+%04X", cp)).toList().toString();
    }
}
