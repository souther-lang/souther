package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import souther.compiler.regex.ConversionAnswers.Seen;

import java.text.Normalizer;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The strings a conversion is seen into a language are those the run time converts into it: every
 * value whose conversion is in the language is among {@code perhaps}, every one of {@code exactly}
 * has its conversion in it, and a string with a code point answered with what the language does
 * not hold is in neither.
 *
 * <p>Held over every value of up to four code points of an alphabet that has the cases that turn
 * on what stands beside them, those that answer several code points, one that answers a code point
 * and a combining mark, the combining marks themselves, and the separator.
 */
class TheStringsASpecialCaseConversionIsSeenIntoAreThoseTheRunTimeConvertsIntoTest {

    private static final UnaryOperator<String> LOWER = text -> Normalizer.normalize(
            text.toLowerCase(Locale.ROOT), Normalizer.Form.NFC);

    private static final UnaryOperator<String> UPPER = text -> Normalizer.normalize(
            text.toUpperCase(Locale.ROOT), Normalizer.Form.NFC);

    private static final int[] ALPHABET = {
        'a', 'b', 'A', 'i', 'I', '@', '.', 0x0130, 0x03A3, 0x03C3, 0x03C2, 0x00DF, 0x1E9E,
        0x01F0, 0x0307, 0x0301, 0x212A, 'k', 'K', 0x0345, 0x03B1};

    private static final int MOST_CODE_POINTS = 4;

    private static final Meter METER = new Meter(100_000, 10_000_000, 1_000_000_000L);

    private static final List<String> LANGUAGES = List.of("[a-z]+", "[a-z.]*", "i|ss|k|ς|σ",
            "[a-z]+\\.[a-z]+", "SS|[A-Z]+", "[a-zσς]+", "i?k?", "[A-Z.]+");

    private static Language language(String regex) {
        Language made = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning()).compile(METER);
        assertNotNull(made, regex);
        return made;
    }

    private static List<String> everyValue() {
        List<String> out = new ArrayList<>(List.of(""));
        List<String> last = List.of("");
        for (int length = 1; length <= MOST_CODE_POINTS; length++) {
            List<String> next = new ArrayList<>();
            for (String shorter : last) {
                for (int each : ALPHABET) {
                    next.add(shorter + Character.toString(each));
                }
            }
            out.addAll(next);
            last = next;
        }
        // What a String holds is in Normalization Form C.
        return out.stream().filter(each -> Normalizer.isNormalized(each, Normalizer.Form.NFC))
                .toList();
    }

    private static void agreesWithTheRunTime(UnaryOperator<String> conversion) {
        ConversionAnswers answers = ConversionAnswers.of(CodeMap.of(conversion), conversion);
        List<String> values = everyValue();
        boolean[] seenSome = {false};
        for (String regex : LANGUAGES) {
            Language into = language(regex);
            Seen seen = answers.stringsSeenInto(into, METER);
            if (seen == null) {
                continue;
            }
            int exact = 0;
            Language image = answers.answersTo(seen.exactly(), METER);
            assertNotNull(image, regex);
            for (String value : values) {
                boolean converts = into.has(conversion.apply(value));
                if (seen.exactly().has(value)) {
                    exact++;
                    assertTrue(converts, () -> regex + " exactly: " + describe(value));
                    assertTrue(image.has(conversion.apply(value)),
                            () -> regex + " image: " + describe(value));
                }
                // What is answered of strings that convert into the language is in it.
                if (image.has(value)) {
                    assertTrue(into.has(value), () -> regex + " image in: " + describe(value));
                }
                if (seen.asLong() && seen.exactly().has(value)) {
                    assertEquals(value.codePointCount(0, value.length()),
                            conversion.apply(value).codePointCount(0,
                                    conversion.apply(value).length()),
                            () -> regex + " as long: " + describe(value));
                }
                if (converts) {
                    assertTrue(seen.perhaps().has(value), () -> regex + " perhaps: "
                            + describe(value));
                }
            }
            seenSome[0] |= exact > 0;
        }
        assertTrue(seenSome[0], "some string is seen into some language exactly");
    }

    private static String describe(String value) {
        StringBuilder out = new StringBuilder();
        value.codePoints().forEach(each -> out.append(String.format("U+%04X ", each)));
        return out.toString();
    }

    @Test
    void lowercaseIsSeenIntoALanguageAsTheRunTimeConvertsIntoIt() {
        agreesWithTheRunTime(LOWER);
    }

    @Test
    void uppercaseIsSeenIntoALanguageAsTheRunTimeConvertsIntoIt() {
        agreesWithTheRunTime(UPPER);
    }

    /** A string with a code point answered with a combining mark is in no language of letters. */
    @Test
    void aCapitalDottedIHoldsNoStringOfLowercaseLetters() {
        ConversionAnswers answers = ConversionAnswers.of(CodeMap.of(LOWER), LOWER);

        Seen seen = answers.stringsSeenInto(language("[a-z]+"), METER);

        assertTrue(seen.exactly().has("ab"));
        assertTrue(seen.exactly().has("AB"));
        assertFalse(seen.perhaps().has("aİ"));
        assertFalse(seen.perhaps().has("İ"));
        assertEquals("ab", LOWER.apply("AB"));
    }

    /** A language that reads a combining mark is not read through the conversion. */
    @Test
    void aLanguageThatReadsAnUnstableCodePointIsNotSeenInto() {
        ConversionAnswers answers = ConversionAnswers.of(CodeMap.of(LOWER), LOWER);

        assertEquals(null, answers.stringsSeenInto(language("[a-ż]+"), METER));
    }

    @Test
    void theSeparatorIsACutOnlyWhereNothingTheConversionDoesReachesAcrossIt() {
        for (UnaryOperator<String> conversion : List.of(LOWER, UPPER)) {
            ConversionAnswers answers = ConversionAnswers.of(CodeMap.of(conversion), conversion);

            assertTrue(answers.cutsAt('@'));
            assertTrue(answers.cutsAt(' '));
            // Cased, and the answer of another code point.
            assertFalse(answers.cutsAt('a'));
            assertFalse(answers.cutsAt('K'));
        }
    }

    /**
     * Where a capital sigma closes a word, a full stop between cased letters is ignored by the
     * lowercase that decides it, so a sigma before it is not a word's last; the uppercase has no
     * such conversion, and nothing stands across it.
     */
    @Test
    void aFullStopIsACutOfTheUppercaseAndNotOfTheLowercase() {
        assertFalse(ConversionAnswers.of(CodeMap.of(LOWER), LOWER).cutsAt('.'));
        assertTrue(ConversionAnswers.of(CodeMap.of(UPPER), UPPER).cutsAt('.'));
    }
}
