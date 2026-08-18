package souther.compiler.check;

/**
 * One question a rule raises, and what it is about.
 *
 * <p>The subject is here because the obligations do not share one. What values may stand somewhere
 * is about a position; where a line falls is about a number taken of one, and a {@code String}
 * bounded on its length raises both — the values are the string's and the line is on the length. A
 * report holding one subject for a rule names the wrong thing for at least one of its questions, and
 * that is how a line about a length came to be printed as a fact about which strings may stand
 * there.
 *
 * <p>Which subject each obligation has follows from the obligation and is settled where the question
 * is raised, so no reader downstream chooses between a path and a term.
 *
 * @param obligation what has to be answered
 * @param subject    what it is about
 */
public record Owed(CoverageObligation obligation, Subject subject) {

    public Owed {
        if (obligation == null || subject == null) {
            throw new IllegalArgumentException("a question with no subject is not one");
        }
    }

    /**
     * What a question is about, as the reading of a value names it.
     *
     * <p>A position of the value, or a number taken of one. The same pair the reading of ends
     * already carries, so that a question and the end that answers it are about the same thing by
     * construction rather than by two spellings agreeing.
     *
     * @param path     where in the value it sits, {@link FieldDomains#THE_VALUE} for the value
     *                 itself
     * @param measured whether it is a count taken of the position rather than the position's own
     *                 value
     */
    public record Subject(String path, boolean measured) {

        public Subject {
            if (path == null) {
                throw new IllegalArgumentException("a subject sits somewhere in the value");
            }
        }

        /** The position's own value. */
        public static Subject at(String path) {
            return new Subject(path, false);
        }

        @Override
        public String toString() {
            // The value itself is at no path, which reads as nothing at all where it is printed.
            String where = path.isEmpty() ? "the value" : path;
            return measured ? "count of " + where : where;
        }
    }
}
