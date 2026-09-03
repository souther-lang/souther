package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The order these machines are built and walked on is {@link String#compareTo} and nothing else.
 *
 * <p>Held to the comparison itself rather than to a table of written answers, because what this is
 * here to catch is a second definition of the order. The symbols a machine steps over are what a
 * matcher reads — a code point where a string holds a well-formed pair — and the runtime compares
 * UTF-16 code units, so the two disagree wherever a pair is involved. A reading that ordered the
 * symbols instead passes every test written over letters and digits.
 *
 * <p>Every string here is written in units, because units are what the question is about.
 * {@code \uD800￿} against {@code 𐀀} is the one that catches the near miss: the two
 * begin with the same unit and spend a different number of them on their first symbol, so no
 * relabelling of the alphabet puts them in the runtime's order — a repair that sorted the symbols by
 * unit rather than by code point would still get it wrong.
 */
class TheRuntimesOrderIsWhatTheseMachinesAnswerAboutTest {

    /** What a language is allowed while one of these is answered. */
    private static Meter allowing() {
        return new Meter(20000, 200000);
    }

    /**
     * Strings crossing every boundary the two orders differ at: the basic plane either side of the
     * surrogates, halves of a pair standing alone, and pairs.
     */
    private static final List<String> STRINGS = List.of(
            "", " ", "a", "ab", "b", "JP", "JPa", "JQ", "J",
            "퟿", "\uD800", "𐀀", "𐏿",
            "\uD800￿", "\uD800\uD800", "􏿿", "\uDC00", "\uDFFF",
            "", " ", "￿", "￿￿",
            "𐀀𐀀", "𐀁", "𐐀");

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
                assertEquals(value.compareTo(than) < 0, before.has(value),
                        shown(value) + " against " + shown(than));
            }
        }
    }

    /**
     * And the strings around one it does not hold, so that the edge is where the comparison puts it
     * and not one unit either side.
     *
     * <p>Every prefix of every string of the corpus, each with one more unit and each with one more
     * unit and the rest. A prefix is below and a string that goes on is above, which is where an
     * off-by-one in the unit walk shows.
     */
    @Test
    void theEdgeIsWhereTheComparisonPutsIt() {
        for (String than : STRINGS) {
            Language before = Language.before(than, allowing());
            assertNotNull(before, shown(than));
            for (String value : around(than)) {
                assertEquals(value.compareTo(than) < 0, before.has(value),
                        shown(value) + " against " + shown(than));
            }
        }
    }

    /** The units a prefix is extended by, which are the ones the two orders part over. */
    private static final char[] UNITS =
            {' ', 'a', '퟿', '\uD800', '\uDBFF', '\uDC00', '\uDFFF', '', '￿'};

    /** A string's prefixes, each on its own and each with one more unit before the rest. */
    private static List<String> around(String than) {
        List<String> out = new ArrayList<>();
        for (int at = 0; at <= than.length(); at++) {
            String prefix = than.substring(0, at);
            out.add(prefix);
            for (char unit : UNITS) {
                out.add(prefix + unit);
                out.add(prefix + unit + than.substring(at));
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
            assertEquals(words.stream().sorted().findFirst().orElseThrow(), wordsOf(words).least(),
                    "the least of " + words.stream().map(
                            TheRuntimesOrderIsWhatTheseMachinesAnswerAboutTest::shown).toList());
        }
    }

    /**
     * The least string a language holds is a string it holds.
     *
     * <p>The law the walk is held to, beside the one about the order. A machine steps over what a
     * matcher reads, so a high surrogate and a low one standing next to each other are the pair and
     * not two symbols — and a walk that took them as two answers with a sequence of symbols no
     * string is written as. Asked whether it holds that, the language says no, and the two answers
     * are about the same string.
     *
     * <p>Over languages built by taking one away from another, which is where such a sequence turns
     * up: the strings above a pair that a prefix of it does not admit begin with the same two units
     * as the prefix does, and only the reading of those units tells them apart.
     */
    @Test
    void theLeastStringALanguageHoldsIsOneItHolds() {
        for (String pattern : List.of("JP[\\s\\S]*", "a*b", "𐀀[\\s\\S]*",
                "[\\s\\S]*", "\uD800[\\s\\S]*", "(JP|US)[\\s\\S]*")) {
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

    /** What a language leaves out from its least string upwards, which is where the two readings of
     *  a pair's units part. */
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
     * The one that tells the two orders apart.
     *
     * <p>The runtime puts the pair first and the symbols put the lone surrogate first, because the
     * pair's first symbol is above every unit. A reading over symbols answers with the wrong one of
     * them whichever way its alphabet is sorted, since the two agree on their first unit and part on
     * how many units that first symbol was.
     */
    @Test
    void aPairAndALoneSurrogateAreOrderedAsTheRuntimeOrdersThem() {
        String pair = "𐀀";
        String lone = "\uD800￿";
        assertTrue(pair.compareTo(lone) < 0, "the runtime puts the pair first");
        assertTrue(pair.codePointAt(0) > lone.codePointAt(0),
                "and the symbols put it second, which is what this is about");

        assertEquals(pair, wordsOf(List.of(pair, lone)).least());

        Language before = Language.before(lone, allowing());
        assertNotNull(before);
        assertTrue(before.has(pair), "the pair comes before the lone surrogate");
        assertFalse(before.has(lone));
    }

    /**
     * The same across the surrogates: a pair is below every string beginning past them.
     *
     * <p>Beside the one above and not a second spelling of it. There, the two strings begin with the
     * same unit, and a walk that took the units to try from the steps as they are written finds that
     * unit anyway — the lone surrogate's own step supplies it, and the pair is reached by accident.
     * Here nothing supplies it: the first units are a high surrogate and one past the surrogates,
     * and a walk that did not take a pair's step apart into the units it spends never offers the
     * first of them. So this is the one place where reading a pair as a unit at a time is what
     * answers, and it is why the walk is written that way.
     */
    @Test
    void aPairIsBelowTheFirstStringPastTheSurrogates() {
        String pair = "𐀀";
        String past = "";
        assertTrue(pair.compareTo(past) < 0);
        assertTrue(pair.codePointAt(0) > past.codePointAt(0));

        assertEquals(pair, wordsOf(List.of(pair, past)).least());
        assertTrue(Language.before(past, allowing()).has(pair));
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
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES);
        assertNotNull(made, pattern + " compiles");
        return made;
    }

    /** A string with its units written out, so that a failure names what it was about. */
    private static String shown(String value) {
        StringBuilder out = new StringBuilder("\"");
        for (int at = 0; at < value.length(); at++) {
            out.append(String.format("\\u%04X", (int) value.charAt(at)));
        }
        return out.append('"').toString();
    }
}
