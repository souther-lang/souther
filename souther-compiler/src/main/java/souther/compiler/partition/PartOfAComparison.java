package souther.compiler.partition;

/**
 * Which of the lines one comparison states is this one, as the reading that took the comparison
 * apart named it.
 *
 * <p>A comparison states one rule, and a rule stating several relations held together draws a line
 * for each of them: {@code Int.max(a, b) <= g} is one rule with a line on {@code a} and one on
 * {@code b}. Which of the two a line is is the answer of the reading that found them, and only
 * that reading makes one — so nothing that meets a line afterwards can number the lines of a
 * comparison by a count of its own, and a reader handed one can only have been handed it.
 *
 * <p>Counted over the relations the statement holds, each once and in the order of their
 * spellings ({@link souther.compiler.meaning.WhereEachLineDecides}). Not over where each was
 * written: one relation stated twice is one line.
 */
public final class PartOfAComparison {

    private final int ordinal;

    PartOfAComparison(int ordinal) {
        if (ordinal < 0) {
            throw new IllegalArgumentException("the lines of a comparison are counted from nought: "
                    + ordinal);
        }
        this.ordinal = ordinal;
    }

    /** Which of the comparison's lines this is, counted from nought. */
    public int ordinal() {
        return ordinal;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof PartOfAComparison that && ordinal == that.ordinal;
    }

    @Override
    public int hashCode() {
        return Integer.hashCode(ordinal);
    }

    @Override
    public String toString() {
        return "line " + ordinal;
    }
}
