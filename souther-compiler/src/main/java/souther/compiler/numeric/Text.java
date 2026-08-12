package souther.compiler.numeric;

/**
 * Where a string sits on its carrier's order, which is the string.
 *
 * <p>The one place with no number under it. A {@code String} is ordered — the language defines
 * {@code <} on it, lexicographically (spec §primitives) — and there is no order-preserving count to
 * embed it into, which is what kept it out of the interval algebra rather than anything about the
 * order itself.
 *
 * <p>So this carries the value and nothing else. What the algebra does with it is compare it against
 * another, tell it from another, and write it down; what the algebra does to a number — step to the
 * next one, take the middle of two, relate it to another position by a difference — it does not do
 * here, and the type is what says so.
 */
public record Text(String at) implements Place {

    public Text {
        if (at == null) {
            throw new IllegalArgumentException("a place is a value; use null for no place");
        }
    }

    public static Text of(String at) {
        return at == null ? null : new Text(at);
    }

    /**
     * The order, which is the strings' own.
     *
     * <p>{@link String#compareTo} and not a collator: the same comparison the runtime makes, so a
     * line drawn here and the branch a row takes cannot disagree about which side of it a value is
     * on. A locale-aware order would put a line somewhere the model did not.
     *
     * <p>Which orders UTF-16 code units and not code points — Java's order, and so the runtime's.
     * Said rather than left to be assumed, because the measure beside this one counts a string's
     * length in code points, on purpose: two units in one measure is the kind of thing read as a
     * mistake later if nothing wrote down that it is not one. What ties them is that each matches
     * what it is a measure of — the length matches what the decoder admits, and the order matches
     * the branch a row takes.
     */
    @Override
    public int compareTo(Place other) {
        if (!(other instanceof Text text)) {
            throw Place.notOneOrder(this, other);
        }
        return at.compareTo(text.at);
    }

    /** What makes two of these one line: the string. There is no second spelling of one to fold. */
    @Override
    public String key() {
        return at;
    }

    @Override
    public String toString() {
        return at;
    }
}
