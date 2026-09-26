package souther.unicode;

/**
 * Text measured and ordered in the unit a {@code String} is made of: Unicode scalar values (spec
 * §string-code-points, §equality).
 *
 * <p>The one statement of both, for everything that measures or orders a {@code String} — the
 * runtime a program runs on and the compiler that folds and reasons about the same values before it
 * runs. Here rather than in the runtime's support classes for the reason {@link Normalization} is:
 * the layers of the compiler that reason about declarations name no backend's package. A reader
 * that measured or ordered text with {@link String#length} or {@link String#compareTo} would be
 * counting UTF-16 code units, which is what a JVM string holds and not what a {@code String} is.
 *
 * <p>Of text that is a sequence of scalar values, which every {@code String} is; nothing here asks.
 */
public final class ScalarValues {

    private ScalarValues() {}

    /** How many scalar values {@code text} is made of: the length the language gives it. */
    public static long count(String text) {
        return text.codePointCount(0, text.length());
    }

    /**
     * Where {@code a} stands against {@code b}: the first scalar value where they differ decides,
     * and where one is a prefix of the other the shorter is below.
     *
     * <p>Not {@link String#compareTo}, which orders UTF-16 code units. The two differ only where the
     * first unit apart begins a pair on one side and is in {@code U+E000..U+FFFF} on the other: a
     * pair stands for a scalar value above every unit, and its first unit is below those. So the
     * units are compared as they are, with that one range moved: a surrogate goes above every other
     * unit. Both sides share every unit before the first one apart, so where one of them is the
     * second half of a pair so is the other, and two second halves keep their order under the move.
     */
    public static int compare(String a, String b) {
        int shared = Math.min(a.length(), b.length());
        for (int at = 0; at < shared; at++) {
            char x = a.charAt(at);
            char y = b.charAt(at);
            if (x != y) {
                return Integer.compare(rank(x), rank(y));
            }
        }
        return Integer.compare(a.length(), b.length());
    }

    /** Where a unit stands among units once a surrogate is put above {@code U+E000..U+FFFF}. */
    private static int rank(char unit) {
        if (unit >= 0xE000) {
            return unit - 0x800;
        }
        return Character.isSurrogate(unit) ? unit + 0x2000 : unit;
    }
}
