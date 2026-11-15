package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The values of a language are those of its strings the run time's normalization leaves as they
 * are, whichever combining marks it holds and wherever they stand.
 *
 * <p>Held over every string of up to four code points of the alphabet the language reads, which
 * has letters that compose with a mark, letters that do not, marks of several combining classes, a
 * mark that stands as a lone one, and the jamo of a Hangul syllable.
 */
class TheValuesOfALanguageAreItsStringsThatAreInNormalFormCTest {

    private static final Meter METER = new Meter(100_000, 10_000_000, 1_000_000_000L);

    private static final int[] ALPHABET = {'a', 'x', 'e', 0x0300, 0x0301, 0x0307, 0x0323, 0x0345,
        0x0327, 0x1100, 0x1161, 0x11A8};

    private static Language language(String regex) {
        Language made = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning()).compile(METER);
        assertNotNull(made, regex);
        return made;
    }

    private static List<String> everyString(int most) {
        List<String> out = new ArrayList<>(List.of(""));
        List<String> last = List.of("");
        for (int length = 1; length <= most; length++) {
            List<String> next = new ArrayList<>();
            for (String shorter : last) {
                for (int each : ALPHABET) {
                    next.add(shorter + Character.toString(each));
                }
            }
            out.addAll(next);
            last = next;
        }
        return out;
    }

    @Test
    void theValuesAreTheStringsTheNormalizationLeavesAsTheyAre() {
        List<String> everyString = everyString(4);
        for (String regex : List.of("[axȩ̣̀́̇ͅ]*",
                "[a-z̀]+", "[ax̣́]*", "[각]*",
                "[axȩ̣̀́̇ͅ각]*")) {
            Language of = language(regex);
            Language values = StringsInNormalFormC.within(of, METER);
            assertNotNull(values, regex);
            for (String each : everyString) {
                boolean value = of.has(each) && Normalization.nfc(each).equals(each);
                assertEquals(value, values.has(each), () -> regex + " "
                        + each.codePoints().mapToObj(cp -> String.format("U+%04X", cp))
                                .toList());
            }
        }
    }

    @Test
    void aLoneCombiningMarkAndOneAfterALetterItComposesWithNothingAreValues() {
        Language values = StringsInNormalFormC.within(language("[xè]+"), METER);

        assertTrue(values.has("̀"));
        assertTrue(values.has("x̀"));
        assertFalse(values.has("è"));
    }

    @Test
    void aLanguageOfStableStartersHoldsOnlyValuesAndIsItsOwn() {
        Language of = language("[a-z]+");

        assertSame(of, StringsInNormalFormC.within(of, METER));
    }
}
