package souther.compiler.observe;

/**
 * Which equivalence class a row's value fell in, or why that could not be decided.
 *
 * <p>Two outcomes rather than a nullable answer, because they mean opposite things to a coverage
 * measure. A row classified somewhere covers that class. A row that could not be classified covers
 * something unknown — and while there is one, a class with no rows is undecided rather than missing.
 * Collapsing the second into "not in this class" turns a measurement that could not look into a gap
 * the author is told to fill.
 */
public sealed interface Classification {

    record Classified(String classId) implements Classification {}

    record Unclassified(Incompleteness reason) implements Classification {}

    static Classification in(String classId) {
        return new Classified(classId);
    }

    static Classification unreadable(Incompleteness.Code code, String subject) {
        return new Unclassified(Incompleteness.of(code, subject));
    }

    default boolean isClassified() {
        return this instanceof Classified;
    }
}
