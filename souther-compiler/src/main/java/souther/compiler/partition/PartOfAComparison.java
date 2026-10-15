package souther.compiler.partition;

import souther.compiler.meaning.WrittenLine;

import java.util.Objects;

/**
 * Which of the lines one comparison states is this one: one its author drew.
 *
 * <p>A comparison states one rule, and its author can draw more than one line with it:
 * {@code Int.max(a, b) <= g} is one rule with a line on {@code a} and one on {@code b}. Those are
 * the arms the comparison's definition takes on the way to a relation ({@link WrittenLine}), and
 * they are the same in every copy of a helper the comparison is read in. What a call hands the
 * definition puts a line somewhere on the behavior's input, and one line can land in many places —
 * one for each case of a value the caller chose — so those places are readings of this line and
 * not lines of their own.
 *
 * <p>Named by the arms alone, read off how the statement was derived ({@code WrittenLines}): what a
 * call hands the definition never splits one of these or joins two.
 */
public final class PartOfAComparison {

    private final WrittenLine line;

    private PartOfAComparison(WrittenLine line) {
        this.line = line;
    }

    /** The line the arms of {@code line} lead to. */
    public static PartOfAComparison of(WrittenLine line) {
        return new PartOfAComparison(Objects.requireNonNull(line, "a part is some written line"));
    }

    /** Which line of the author's this is. */
    public WrittenLine line() {
        return line;
    }

    /** Whether this is the comparison itself, which its author drew as one line. */
    public boolean isTheComparison() {
        return line.arms().isEmpty();
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof PartOfAComparison that && line.equals(that.line);
    }

    @Override
    public int hashCode() {
        return line.hashCode();
    }

    @Override
    public String toString() {
        return "line " + line.arms();
    }
}
