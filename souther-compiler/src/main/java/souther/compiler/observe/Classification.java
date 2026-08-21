package souther.compiler.observe;

/**
 * Which equivalence classes a row's values at one position fell in, or why that could not be
 * decided.
 *
 * <p>Two outcomes rather than a nullable answer, because they mean opposite things to a coverage
 * measure. A row classified somewhere covers that class. A row that could not be classified covers
 * something unknown — and while there is one, a class with no rows is undecided rather than missing.
 * Collapsing the second into "not in this class" turns a measurement that could not look into a gap
 * the author is told to fill.
 *
 * <p>Classes and not a class. A position inside a sequence has as many values as the row wrote
 * there, and they need not fall together: a list holding one element under a line and one over it
 * covers the classes either side of that line, and there is no element among them a reading is
 * entitled to pick. Everywhere else there is one value and so one class, which is the same answer
 * said in the plural.
 */
public sealed interface Classification {

    /**
     * The classes the row's values at the position fell in.
     *
     * <p>Empty is an answer and not an absence: a row whose list holds no element was read there
     * and is in none of the classes, which is a different thing from a row nothing could read. Read
     * as the second, an author would be told a measurement could not look where it looked and found
     * nothing to see.
     */
    record Classified(java.util.List<String> classIds) implements Classification {

        public Classified {
            classIds = java.util.List.copyOf(classIds);
        }
    }

    record Unclassified(Incompleteness reason) implements Classification {}

    static Classification in(String classId) {
        return new Classified(java.util.List.of(classId));
    }

    /** The same, of a position whose values fell in more than one. */
    static Classification in(java.util.List<String> classIds) {
        return new Classified(classIds);
    }

    static Classification unreadable(Incompleteness.Code code, String behavior, String path) {
        return new Unclassified(Incompleteness.atPosition(code, behavior, path));
    }

    default boolean isClassified() {
        return this instanceof Classified;
    }
}
