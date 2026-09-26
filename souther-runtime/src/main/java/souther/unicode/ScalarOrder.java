package souther.unicode;

/**
 * The lexicographic order of two texts over their Unicode scalar values: the order the language
 * puts {@code String}s in (spec §equality), and the order the compiler reasons about text in.
 *
 * <p>Here rather than in the runtime's support classes for the reason {@link Normalization} is:
 * it is a fact about Unicode text that the compiler reasons with and a program runs, and the layers
 * of the compiler that reason about declarations name no backend's package.
 */
public final class ScalarOrder {

    private ScalarOrder() {}

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
     *
     * <p>Of text that is a sequence of scalar values, which every {@code String} is; nothing here
     * asks.
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
