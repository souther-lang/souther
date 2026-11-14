package souther.compiler.check;

import java.util.ArrayList;
import java.util.List;

/**
 * Which statement of a conjunct a statement is, and which statements it is within.
 *
 * <p>A statement of the conjunct is counted from nought over all of them. What a container states of
 * every element is a predicate, which states things of its own, and each of them is numbered within
 * the statement of the container that says it: counted in the conjunct they would be the numbers of
 * statements the container's reading of that conjunct already holds, and counted afresh wherever
 * the elements are read, two statements of one conjunct would be one.
 *
 * <p>Held apart from the conjunct so that a statement's identity ({@link InvariantStatementId}) has
 * one way to the rule it is about, which is the conjunct, and what this adds to it has none.
 *
 * @param ordinal which of its statements it is, counted from zero over all of them
 * @param inside  the numbers of the statements it is within, the outermost first: none for a
 *                statement of the conjunct itself
 */
public record StatementNumber(int ordinal, List<Integer> inside) {

    public StatementNumber {
        if (ordinal < 0) {
            throw new IllegalArgumentException(
                    "a statement of a conjunct is counted from zero: " + ordinal);
        }
        inside = List.copyOf(inside);
    }

    /** The statement {@code ordinal} of a conjunct, as an author wrote it. */
    public static StatementNumber of(int ordinal) {
        return new StatementNumber(ordinal, List.of());
    }

    /** The statement {@code ordinal} of what this one states of every element. */
    public StatementNumber stating(int ordinal) {
        List<Integer> within = new ArrayList<>(inside);
        within.add(this.ordinal);
        return new StatementNumber(ordinal, within);
    }

    @Override
    public String toString() {
        return inside.isEmpty() ? String.valueOf(ordinal) : ordinal + " in " + inside;
    }
}
