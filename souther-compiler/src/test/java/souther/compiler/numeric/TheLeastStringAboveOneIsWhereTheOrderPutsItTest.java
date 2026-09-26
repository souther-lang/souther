package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.runtime.Strings;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What is just above a string is held to {@link Strings#compare}, like everything else about the
 * order.
 *
 * <p>The claim is two things and both are checked against the comparison itself: the answer is above
 * the string, and no string is between the two. A reading that answered with the string and one more
 * of the wrong character would satisfy the first and not the second, and a run holding a single
 * value would be told apart from one holding more by an answer that is merely somewhere above.
 */
class TheLeastStringAboveOneIsWhereTheOrderPutsItTest {

    /** The text of these code points. */
    private static String text(int... codePoints) {
        return new String(codePoints, 0, codePoints.length);
    }

    /** Strings crossing the places the language's order and the units' order part at. */
    private static final List<String> STRINGS = List.of(
            "", " ", "a", "ab", "JP", "JQ", text(0xD7FF), text(0x10000), text(0x10FFFF),
            text(0xE000), text(0xFFE5), text(0xFFFF), text(0xFFFF, 0xFFFF), text(0x20BB7));

    /** It is above, and nothing among the strings there are is between. */
    @Test
    void nothingIsBetweenAStringAndTheOneJustAboveIt() {
        for (String each : STRINGS) {
            String above = Text.of(each).justAbove().at();
            assertTrue(Strings.compare(each, above) < 0,
                    shown(above) + " is above " + shown(each));
            for (String other : between(each)) {
                assertTrue(Strings.compare(other, each) <= 0 || Strings.compare(other, above) >= 0,
                        shown(other) + " is between " + shown(each) + " and " + shown(above));
            }
        }
    }

    /** The strings closest to {@code than}: itself with one more character, and its prefixes with
     *  one. */
    private static List<String> between(String than) {
        List<String> out = new java.util.ArrayList<>();
        int[] symbols = than.codePoints().toArray();
        for (int at = 0; at <= symbols.length; at++) {
            String prefix = text(java.util.Arrays.copyOf(symbols, at));
            String rest = text(java.util.Arrays.copyOfRange(symbols, at, symbols.length));
            for (int character : new int[] {0, 1, ' ', 'a', 0xE000, 0xFFFF, 0x10000, 0x10FFFF}) {
                out.add(prefix + text(character));
                out.add(prefix + text(character) + rest);
            }
        }
        out.addAll(STRINGS);
        return out;
    }

    private static String shown(String value) {
        StringBuilder out = new StringBuilder("\"");
        value.codePoints().forEach(each -> out.append(String.format("U+%04X ", each)));
        return out.append('"').toString();
    }
}
