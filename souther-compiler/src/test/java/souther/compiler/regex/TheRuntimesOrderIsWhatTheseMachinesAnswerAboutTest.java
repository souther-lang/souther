package souther.compiler.regex;

import org.junit.jupiter.api.Test;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The order these machines are built and walked on is {@link Strings#compare} and nothing else.
 *
 * <p>Held to the comparison itself rather than to a table of written answers, because what this is
 * here to catch is a second definition of the order. {@link String#compareTo} is the one a
 * reader reaches for first, and it passes every test written over letters and digits: it parts
 * from the language's order only where a character past the basic plane meets one in
 * {@code U+E000..U+FFFF}, which is where the corpus below is dense.
 */
class TheRuntimesOrderIsWhatTheseMachinesAnswerAboutTest {

    /** What a language is allowed while one of these is answered. */
    private static Meter allowing() {
        return new Meter(20000, 200000);
    }

    /** The text of these code points. */
    private static String text(int... codePoints) {
        return new String(codePoints, 0, codePoints.length);
    }

    /**
     * Strings crossing every place the two orders differ at: the basic plane either side of the
     * surrogates, the top of the basic plane, and characters past it.
     */
    private static final List<String> STRINGS = List.of(
            "", " ", "a", "ab", "b", "JP", "JPa", "JQ", "J",
            text(0xD7FF), text(0xE000), text(0xFFE5), text(0xFFFF), text(0xFFFF, 0xFFFF),
            text(0x10000), text(0x103FF), text(0x10FFFF), text(0x10000, 0x10000),
            text(0x10001), text(0x10400), text(0x20BB7), text(0x20BB7, 'a'), text(0xE000, 0x10000));

    /**
     * The machine for what comes before a string accepts exactly the strings that do.
     *
     * <p>Over every pair of the corpus, both ways round, so that what is checked is the comparison
     * and not one side of it.
     */
    @Test
    void whatComesBeforeAStringIsWhatTheRuntimeSaysComesBeforeIt() {
        for (String than : STRINGS) {
            Language before = Language.before(than, allowing());
            assertNotNull(before, "the machine for what comes before " + shown(than));
            for (String value : STRINGS) {
                assertEquals(Strings.compare(value, than) < 0, before.has(value),
                        shown(value) + " against " + shown(than));
            }
        }
    }

    /**
     * And the strings around one it does not hold, so that the edge is where the comparison puts it
     * and not one character either side.
     *
     * <p>Every prefix of every string of the corpus, each with one more character and each with one
     * more character and the rest. A prefix is below and a string that goes on is above, which is
     * where an off-by-one in the walk shows.
     */
    @Test
    void theEdgeIsWhereTheComparisonPutsIt() {
        for (String than : STRINGS) {
            Language before = Language.before(than, allowing());
            assertNotNull(before, shown(than));
            for (String value : around(than)) {
                assertEquals(Strings.compare(value, than) < 0, before.has(value),
                        shown(value) + " against " + shown(than));
            }
        }
    }

    /** The characters a prefix is extended by, which are the ones the two orders part over. */
    private static final int[] CHARACTERS =
            {0, ' ', 'a', 0xD7FF, 0xE000, 0xFFE5, 0xFFFF, 0x10000, 0x20BB7, 0x10FFFF};

    /** A string's prefixes, each on its own and each with one more character before the rest. */
    private static List<String> around(String than) {
        List<String> out = new ArrayList<>();
        for (int at = 0; at <= than.length(); at = at + (at < than.length()
                ? Character.charCount(than.codePointAt(at)) : 1)) {
            String prefix = than.substring(0, at);
            out.add(prefix);
            for (int character : CHARACTERS) {
                out.add(prefix + text(character));
                out.add(prefix + text(character) + than.substring(at));
            }
        }
        return out;
    }

    /**
     * The least string a language holds is the one the comparison puts first.
     *
     * <p>Read against the corpus rather than against a written answer: such a language is the words
     * themselves, so what it has to answer is whichever of them comes first.
     */
    @Test
    void theLeastStringIsTheOneTheComparisonPutsFirst() {
        for (int held = 1; held <= STRINGS.size(); held++) {
            List<String> words = STRINGS.subList(0, held);
            assertEquals(words.stream().sorted(Strings::compare).findFirst().orElseThrow(),
                    wordsOf(words).least(),
                    "the least of " + words.stream().map(
                            TheRuntimesOrderIsWhatTheseMachinesAnswerAboutTest::shown).toList());
        }
    }

    /**
     * The least string a language holds is a string it holds.
     *
     * <p>Over languages built by taking one away from another as well as over patterns, which is
     * where a walk that chose a symbol leading nowhere would answer with something the language
     * turns away.
     */
    @Test
    void theLeastStringALanguageHoldsIsOneItHolds() {
        for (String pattern : List.of("JP[\\s\\S]*", "a*b", text(0x10000) + "[\\s\\S]*",
                "[\\s\\S]*", text(0xFFE5) + "[\\s\\S]*", "(JP|US)[\\s\\S]*")) {
            for (Language each : List.of(of(pattern), leftOver(of(pattern)))) {
                String least = each.least();
                if (least != null) {
                    assertTrue(each.has(least),
                            shown(least) + " is answered as the least of a language that does not"
                                    + " hold it, from " + pattern);
                }
            }
        }
    }

    /** What a language does not hold is what every string it does not hold is. */
    @Test
    void whatALanguageDoesNotHoldIsEveryStringItDoesNotHold() {
        for (String pattern : List.of("JP[\\s\\S]*", "a*b", text(0x10000) + "[\\s\\S]*",
                text(0xE000) + "[\\s\\S]*")) {
            Language one = of(pattern);
            Language rest = one.not(allowing());
            assertNotNull(rest, pattern);
            for (String value : STRINGS) {
                assertEquals(!one.has(value), rest.has(value),
                        shown(value) + " against what " + pattern + " does not hold");
            }
        }
    }

    /** And a language holding every string says so, however it was arrived at. */
    @Test
    void aLanguageHoldingEveryStringSaysSo() {
        assertTrue(of("[\\s\\S]*").isEverything());
        assertTrue(Language.EVERY_STRING.isEverything());
        Language something = of("JP[\\s\\S]*");
        assertTrue(something.or(something.not(allowing()), allowing()).isEverything(),
                "a language and what it leaves out are every string there is");
        assertFalse(of("a*b").isEverything());
    }

    /** What a language leaves out from its least string upwards. */
    private static Language leftOver(Language language) {
        Meter meter = allowing();
        String least = language.least();
        if (least == null) {
            return language;
        }
        Language above = Language.before(least, meter).not(meter);
        return above.and(language.not(meter), meter);
    }

    /** A language with nothing in it has no least string, which is not a string it holds. */
    @Test
    void aLanguageHoldingNothingHasNoLeast() {
        Language nothing = wordsOf(List.of("a")).and(wordsOf(List.of("b")), allowing());
        assertNotNull(nothing);
        assertTrue(nothing.isEmpty());
        assertNull(nothing.least());
    }

    /**
     * A language whose strings descend without stopping has no least, and says so rather than
     * answering with one it reached.
     *
     * <p>{@code a*b} holds {@code b}, and {@code ab} below it, and {@code aab} below that: every
     * string of it has one below it, and what is below all of them is not a string. Answered with
     * the shortest, a reading would put a line at {@code b} and call it where the values stop.
     */
    @Test
    void aLanguageDescendingWithoutStoppingHasNoLeast() {
        Language descending = of("a*b");
        assertTrue(descending.has("b"));
        assertTrue(descending.has("aaab"));
        assertNull(descending.least());
    }

    /** A prefix has one: every string it holds begins with it, so it is the least of them. */
    @Test
    void aPrefixIsTheLeastOfWhatItAdmits() {
        assertEquals("JP", of("JP[\\s\\S]*").least());
    }

    /**
     * The pair that tells the two orders apart.
     *
     * <p>{@code ￥} is U+FFE5 and {@code 𠮷} is U+20BB7, so the language puts {@code ￥} first; the
     * first unit of {@code 𠮷} is D842, below FFE5, so a comparison of units puts it second. A reading
     * that took its order from {@link String#compareTo} answers with the other one.
     */
    @Test
    void aCharacterPastTheBasicPlaneIsAboveEveryCharacterInIt() {
        String yen = text(0xFFE5);
        String yoshi = text(0x20BB7);
        assertTrue(Strings.compare(yen, yoshi) < 0, "the language puts U+FFE5 first");
        assertTrue(yen.compareTo(yoshi) > 0, "and the units put it second, which is what this is about");

        assertEquals(yen, wordsOf(List.of(yoshi, yen)).least());

        Language beforeYoshi = Language.before(yoshi, allowing());
        assertNotNull(beforeYoshi);
        assertTrue(beforeYoshi.has(yen), "U+FFE5 comes before U+20BB7");
        assertFalse(Language.before(yen, allowing()).has(yoshi));
    }

    /** The language holding exactly {@code words}. */
    private static Language wordsOf(List<String> words) {
        Meter meter = allowing();
        Automaton made = Automaton.ofWords(words, meter);
        assertNotNull(made, "a machine for " + words.size() + " words");
        Automaton canonical = made.canonical(meter);
        assertNotNull(canonical);
        return new Language(canonical);
    }

    /** The language of one written pattern, which is what a rule states. */
    private static Language of(String pattern) {
        PatternRead read = PatternParser.read(pattern);
        assertTrue(read instanceof PatternRead.Read, pattern + " is read");
        Language made = PatternPlan.of(((PatternRead.Read) read).syntax())
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
        assertNotNull(made, pattern + " compiles");
        return made;
    }

    /** A string with its code points written out, so that a failure names what it was about. */
    private static String shown(String value) {
        StringBuilder out = new StringBuilder("\"");
        value.codePoints().forEach(each -> out.append(String.format("U+%04X ", each)));
        return out.append('"').toString();
    }
}
