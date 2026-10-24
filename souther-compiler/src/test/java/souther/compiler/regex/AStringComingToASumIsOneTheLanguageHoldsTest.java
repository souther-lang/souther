package souther.compiler.regex;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.IntPredicate;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A string a language holds whose code points come to a number is found exactly where one exists,
 * and is one the language holds, coming to that number, of a length asked for.
 *
 * <p>The oracle is every string over a few code points up to a length, each asked of the language
 * by {@link Language#has} and added up here: so a sum the walk misses, a sum it claims that no
 * string reaches, and a string it offers that the language refuses are each a difference from it.
 * The code points are chosen so that the sums have gaps, a code point no row can show is among
 * them, and the languages loop.
 */
class AStringComingToASumIsOneTheLanguageHoldsTest {

    private static final int WORK = 1_000_000;

    private static Meter roomy() {
        return new Meter(100_000, 10_000_000, 1_000_000_000L);
    }

    private static Language language(String regex) {
        Language made = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning()).compile(roomy());
        assertNotNull(made, regex);
        return made;
    }

    /** The string {@code language} offers for {@code sum}, or null where it says none comes to it;
     *  never past the work, which these languages are small enough not to reach. */
    private static String comingTo(Language language, long sum, IntPredicate lengths, int longest,
                                   CodePoints preferred) {
        return switch (language.comingTo(sum, lengths, longest, preferred, WORK)) {
            case Language.ComingTo.Written(String text) -> text;
            case Language.ComingTo.NoneDoes _ -> null;
            case Language.ComingTo.PastTheWork _ ->
                    throw new AssertionError(language + " ran out of work at " + sum);
        };
    }

    /** For each sum, the shortest length a string of the language over {@code alphabet} with no
     *  control code comes to it at, up to {@code longest}. */
    private static Map<Long, Integer> shortestAtEachSum(Language language, int[] alphabet,
                                                        int longest) {
        Map<Long, Integer> out = new TreeMap<>();
        List<int[]> layer = new ArrayList<>(List.of(new int[0]));
        for (int length = 0; length <= longest; length++) {
            List<int[]> next = new ArrayList<>();
            for (int[] each : layer) {
                String text = new String(each, 0, each.length);
                boolean written = text.codePoints().noneMatch(
                        c -> Character.getType(c) == Character.CONTROL
                                && c != '\t' && c != '\n' && c != '\r');
                if (written && language.has(text)) {
                    out.putIfAbsent(text.codePoints().asLongStream().sum(), length);
                }
                for (int symbol : alphabet) {
                    int[] longer = Arrays.copyOf(each, each.length + 1);
                    longer[each.length] = symbol;
                    next.add(longer);
                }
            }
            layer = next;
        }
        return out;
    }

    private static void agreesWithEveryString(String regex, int[] alphabet, int longest) {
        Language language = language(regex);
        Map<Long, Integer> expected = shortestAtEachSum(language, alphabet, longest);
        long most = alphabet[alphabet.length - 1] * (long) longest;
        for (long sum = 0; sum <= most; sum++) {
            String found = comingTo(language, sum, length -> true, longest, CodePoints.NONE);
            if (!expected.containsKey(sum)) {
                assertNull(found, regex + " holds no written string of " + longest
                        + " code points or fewer coming to " + sum);
                continue;
            }
            assertNotNull(found, regex + " holds a string coming to " + sum);
            assertTrue(language.has(found), () -> regex + " holds what was offered for it");
            assertEquals(sum, found.codePoints().asLongStream().sum(), regex);
            assertEquals(expected.get(sum), found.codePointCount(0, found.length()),
                    () -> regex + " is offered the shortest string coming to the sum");
        }
    }

    /** A fixed length of one run of code points, where every sum between the least and the most
     *  is reached. */
    @Test
    void aFixedLengthOfOneRunReachesEverySumBetweenItsEnds() {
        agreesWithEveryString("[0-3]{3}", new int[] {'0', '1', '2', '3'}, 3);
    }

    /** Code points with a gap between them, so the sums of a length have gaps too. */
    @Test
    void codePointsApartLeaveSumsNoStringReaches() {
        agreesWithEveryString("[ac]{1,3}", new int[] {'a', 'b', 'c'}, 3);
    }

    /** Alternatives of different lengths and a loop, where one sum is reached at several lengths
     *  and the shortest is offered. */
    @Test
    void aLoopReachesASumAtTheShortestLengthItCan() {
        agreesWithEveryString("(ab)*c|b{2,}", new int[] {'a', 'b', 'c'}, 5);
    }

    /** A control code no row can show is never one of the code points, even where it alone would
     *  reach the sum. */
    @Test
    void aCodePointNoRowShowsIsNeverWritten() {
        agreesWithEveryString("[\\x{0}\\x{1}a]{2}", new int[] {0, 1, 'a'}, 2);
        assertNull(comingTo(language("[\\x{0}a]{2}"), 97, length -> true, 2, CodePoints.NONE));
    }

    /** Only lengths asked for are offered, and a sum reached only at another length is not. */
    @Test
    void onlyALengthAskedForIsOffered() {
        Language digits = language("[0-9]+");
        String three = comingTo(digits, 150, length -> length == 3, 100, CodePoints.NONE);
        assertNotNull(three);
        assertEquals(3, three.length());
        assertEquals(150, three.codePoints().sum());
        // Three digits come to no more than 171.
        assertNull(comingTo(digits, 172, length -> length == 3, 100, CodePoints.NONE));
    }

    /** A thirteen-digit code comes to each sum from thirteen of the least digit to thirteen of the
     *  greatest, each with a string of thirteen digits. */
    @Test
    void thirteenDigitsComeToEverySumThirteenDigitsSpan() {
        Language barcode = language("[0-9]{13}");
        for (long sum = 13 * '0'; sum <= 13 * '9'; sum++) {
            String found = comingTo(barcode, sum, length -> true, 100, CodePoints.NONE);
            assertNotNull(found, "thirteen digits come to " + sum);
            assertTrue(barcode.has(found));
            assertEquals(sum, found.codePoints().asLongStream().sum());
        }
        assertNull(comingTo(barcode, 13 * '0' - 1, length -> true, 100, CodePoints.NONE));
        assertNull(comingTo(barcode, 13 * '9' + 1, length -> true, 100, CodePoints.NONE));
    }

    /** Preferred code points are chosen wherever they reach the sum. */
    @Test
    void thePreferredCodePointsAreChosenWhereTheyReachTheSum() {
        String found = comingTo(language("[0-9]{2}"), '5' + '5', length -> true, 2,
                CodePoints.between('5', '9'));
        assertEquals("55", found);
    }

    /**
     * The least and the greatest sum are those of the strings themselves, control codes among
     * them, and a language that loops has no greatest.
     */
    @Test
    void theSumsLieBetweenTheLeastAndTheGreatestAStringComesTo() {
        assertEquals(new Language.SumsOfCodePoints(3 * '0', (long) 3 * '3'),
                language("[0-3]{3}").sumsOfCodePoints());
        assertEquals(new Language.SumsOfCodePoints('a', (long) 3 * 'c'),
                language("[ac]{1,3}").sumsOfCodePoints());
        assertEquals(new Language.SumsOfCodePoints(0, 2L * 'a'),
                language("[\\x{0}a]{2}").sumsOfCodePoints());
        assertEquals(new Language.SumsOfCodePoints('c', null),
                language("(ab)*c|b{2,}").sumsOfCodePoints());
        assertEquals(new Language.SumsOfCodePoints(0, 0L), language("").sumsOfCodePoints());
        assertNull(language("a").and(language("b"), roomy()).sumsOfCodePoints());
    }

    /** Past the work allowed nothing is offered, and that is said apart from there being none. */
    @Test
    void pastTheWorkAllowedIsSaidApartFromThereBeingNone() {
        assertInstanceOf(Language.ComingTo.PastTheWork.class,
                language("[0-9]{13}").comingTo(700, length -> true, 100, CodePoints.NONE, 3));
        assertInstanceOf(Language.ComingTo.NoneDoes.class,
                language("[0-9]{13}").comingTo(800, length -> true, 100, CodePoints.NONE, WORK));
    }
}
