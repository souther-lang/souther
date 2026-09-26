package souther.compiler.numeric;

import souther.unicode.ScalarValues;

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
     * The order, which is the language's order on text.
     *
     * <p>{@link ScalarValues#compare} and not a collator: the same comparison the runtime makes, so a
     * line drawn here and the branch a row takes cannot disagree about which side of it a value is
     * on. A locale-aware order would put a line somewhere the model did not. And not
     * {@link String#compareTo}, which orders UTF-16 code units and would put a line between a
     * character past the basic plane and one in {@code U+E000..U+FFFF} on the other side of where
     * the runtime puts it.
     */
    @Override
    public int compareTo(Place other) {
        if (!(other instanceof Text text)) {
            throw Place.notOneOrder(this, other);
        }
        return ScalarValues.compare(at, text.at);
    }

    /**
     * The least string above this one, which every string has.
     *
     * <p>The order has no predecessor and this is not one: a string above another either begins
     * with it and goes on, or parts from it at a character and is above every string that begins
     * with it — so the least of them is this string and U+0000, the least character there is. What
     * has no answer is
     * the other direction, which is why a row just below a line cannot be written
     * ({@link souther.compiler.check.Carrier.Text}).
     *
     * <p>Here because the order is here. A reader working out whether two places have anything
     * between them is asking about the order, and one that spelled the answer for itself would be a
     * second definition of what "just above" means.
     */
    public Text justAbove() {
        return new Text(at + (char) 0);
    }

    /** What makes two of these one line: the string. There is no second spelling of one to fold. */
    @Override
    public String key() {
        return at;
    }

    /** The string, which is what a reader of one is shown and what tells two of them apart both. A
     *  string is its own name, so there is nothing here the other question does not already ask. */
    @Override
    public String spelled() {
        return at;
    }

    /** Itself, there being no second spelling of a string to fold. */
    @Override
    public Text canonical() {
        return this;
    }

    @Override
    public String toString() {
        return at;
    }
}
