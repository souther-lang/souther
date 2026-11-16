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
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
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
 * <p>Held over every value of up to two code points of an alphabet that has the cases that turn
 * on what stands beside them, those that answer several code points, one that answers a code point
 * and a combining mark, the combining marks themselves, and the separator.
 */
class TheStringsASpecialCaseConversionIsSeenIntoAreThoseTheRunTimeConvertsIntoTest {

    static final UnaryOperator<String> LOWER =
            TheStringsASpecialCaseConversionIsSeenIntoAreThoseTheRunTimeConvertsIntoTest::lowered;

    static final UnaryOperator<String> UPPER =
            TheStringsASpecialCaseConversionIsSeenIntoAreThoseTheRunTimeConvertsIntoTest::uppered;

    private static String lowered(String text) {
        return Normalizer.normalize(text.toLowerCase(Locale.ROOT), Normalizer.Form.NFC);
    }

    private static String uppered(String text) {
        return Normalizer.normalize(text.toUpperCase(Locale.ROOT), Normalizer.Form.NFC);
    }

    /** Beside the rest, a dotless {@code ı}, whose capital is composed with a dot above after it
     *  into {@code İ}, and an {@code e} and its composites with an acute. */
    private static final int[] ALPHABET = {
        'a', 'b', 'A', 'i', 'I', '@', '.', 0x0130, 0x03A3, 0x03C3, 0x03C2, 0x00DF, 0x1E9E,
        0x01F0, 0x0307, 0x0301, 0x212A, 'k', 'K', 0x0345, 0x03B1, 0x0131, 'e', 0x00E9, 0x00C9};

    /** What a conversion turns on is what stands beside a code point, so two code points hold each
     *  of the cases that matter, and a value of a second is what a change to the answers is asked
     *  of at once. Three, which put a code point between two others, are asked at night
     *  ({@link EveryValueOfThreeCodePointsIsSeenIntoALanguageAsTheRunTimeConvertsItTest}). */
    private static final int MOST_CODE_POINTS = 2;

    private static final Meter METER = new Meter(100_000, 10_000_000, 1_000_000_000L);

    /** Beside languages of letters with no composite, languages of composites a conversion's
     *  answer may be composed into. */
    private static final List<String> LANGUAGES = List.of("[a-z]+", "[a-z.]*", "i|ss|k|ς|σ",
            "[a-z]+\\.[a-z]+", "SS|[A-Z]+", "[a-zσς]+", "i?k?", "[A-Z.]+", "\\x{130}",
            "[A-Z\\x{130}\\x{C9}]+", "[a-z\\x{E9}]+");

    private static Language language(String regex) {
        Language made = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning()).compile(METER);
        assertNotNull(made, regex);
        return made;
    }

    /** What each conversion answers of each code point, read once: a map is made by asking the
     *  conversion of every code point there is. */
    private static final Map<UnaryOperator<String>, ConversionAnswers> ANSWERS =
            new ConcurrentHashMap<>();

    private static ConversionAnswers answersOf(UnaryOperator<String> conversion) {
        return ANSWERS.computeIfAbsent(conversion,
                each -> ConversionAnswers.of(CodeMap.of(each), each));
    }

    /** Every value of up to the most code points, made once for the tests that ask of all. */
    private static final List<String> EVERY_VALUE = everyValue(MOST_CODE_POINTS);

    /** Every value of the alphabet of up to {@code most} code points that a {@code String} holds. */
    static List<String> everyValue(int most) {
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
        // What a String holds is in Normalization Form C.
        return out.stream().filter(each -> Normalizer.isNormalized(each, Normalizer.Form.NFC))
                .toList();
    }

    /** That what is seen of {@code conversion} into each language agrees, over {@code values},
     *  with what the run time converts. */
    static void agreesWithTheRunTime(UnaryOperator<String> conversion, List<String> values) {
        ConversionAnswers answers = answersOf(conversion);
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
        agreesWithTheRunTime(LOWER, EVERY_VALUE);
    }

    @Test
    void uppercaseIsSeenIntoALanguageAsTheRunTimeConvertsIntoIt() {
        agreesWithTheRunTime(UPPER, EVERY_VALUE);
    }

    /** A string with a code point answered with a combining mark is in no language of letters. */
    @Test
    void aCapitalDottedIHoldsNoStringOfLowercaseLetters() {
        ConversionAnswers answers = answersOf(LOWER);

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
        ConversionAnswers answers = answersOf(LOWER);

        assertEquals(null, answers.stringsSeenInto(language("[a-ż]+"), METER));
    }

    @Test
    void theSeparatorIsACutOnlyWhereNothingTheConversionDoesReachesAcrossIt() {
        for (UnaryOperator<String> conversion : List.of(LOWER, UPPER)) {
            ConversionAnswers answers = answersOf(conversion);

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
        assertFalse(answersOf(LOWER).cutsAt('.'));
        assertTrue(answersOf(UPPER).cutsAt('.'));
    }
}
