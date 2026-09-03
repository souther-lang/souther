package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What is just above a string is held to {@link String#compareTo}, like everything else about the
 * order.
 *
 * <p>The claim is two things and both are checked against the comparison itself: the answer is above
 * the string, and no string is between the two. A reading that answered with the string and one more
 * of the wrong unit would satisfy the first and not the second, and a run holding a single value
 * would be told apart from one holding more by an answer that is merely somewhere above.
 */
class TheLeastStringAboveOneIsWhereTheOrderPutsItTest {

    /** Strings crossing the boundaries the order is written in units over. */
    private static final List<String> STRINGS = List.of(
            "", " ", "a", "ab", "JP", "JQ", "퟿", "\uD800", "𐀀", "􏿿",
            "\uD800￿", "\uDC00", "\uDFFF", "", "￿", "￿￿");

    /** It is above, and nothing among the strings there are is between. */
    @Test
    void nothingIsBetweenAStringAndTheOneJustAboveIt() {
        for (String each : STRINGS) {
            String above = Text.of(each).justAbove().at();
            assertTrue(each.compareTo(above) < 0,
                    shown(above) + " is above " + shown(each));
            for (String other : between(each)) {
                assertTrue(other.compareTo(each) <= 0 || other.compareTo(above) >= 0,
                        shown(other) + " is between " + shown(each) + " and " + shown(above));
            }
        }
    }

    /** The strings closest to {@code than}: itself with one more unit, and its prefixes with one. */
    private static List<String> between(String than) {
        List<String> out = new java.util.ArrayList<>();
        for (int at = 0; at <= than.length(); at++) {
            for (char unit : new char[] {0, 1, ' ', 'a', '\uD800', '\uDC00', '￿'}) {
                out.add(than.substring(0, at) + unit);
                out.add(than.substring(0, at) + unit + than.substring(at));
            }
        }
        out.addAll(STRINGS);
        return out;
    }

    private static String shown(String value) {
        StringBuilder out = new StringBuilder("\"");
        for (int at = 0; at < value.length(); at++) {
            out.append(String.format("\\u%04X", (int) value.charAt(at)));
        }
        return out.append('"').toString();
    }
}
