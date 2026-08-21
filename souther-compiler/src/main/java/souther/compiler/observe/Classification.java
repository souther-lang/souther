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
 *
 * <p>And which element gave which class, which the classes alone cannot say. A relation between two
 * positions is about one element standing in both, and two sets of classes read off one row hold
 * every combination of them — so a row whose first element is under a line and whose second is
 * active would be evidence for an element both over the line and active, which none of them is. The
 * element each class came from is carried for that reason and for no other: what a single position
 * covers is the classes, whichever elements gave them.
 */
public sealed interface Classification {

    /** Why something here could not be read, or null where everything was. */
    Incompleteness stopped();

    /**
     * The classes the row's values at the position fell in.
     *
     * <p>Empty is an answer and not an absence: a row whose list holds no element was read there
     * and is in none of the classes, which is a different thing from a row nothing could read. Read
     * as the second, an author would be told a measurement could not look where it looked and found
     * nothing to see.
     */
    record Classified(java.util.List<At> at, Incompleteness stopped) implements Classification {

        public Classified {
            at = java.util.List.copyOf(at);
        }

        /**
         * Why some value here could not be placed, or null where every one was.
         *
         * <p>Beside the classes rather than instead of them. A list holding one value a class holds
         * and one nothing could read covers that class and is short of what the rest of it says, and
         * the two are different facts about one row: read as one, either the coverage is thrown away
         * or the measurement is called complete over a value nothing looked at.
         */
        @Override
        public Incompleteness stopped() {
            return stopped;
        }

        /** The classes the row's values fell in, whichever elements gave them. */
        public java.util.List<String> classIds() {
            java.util.List<String> out = new java.util.ArrayList<>();
            for (At each : at) {
                if (!out.contains(each.classId())) {
                    out.add(each.classId());
                }
            }
            return java.util.List.copyOf(out);
        }
    }

    /**
     * One value's class, and which element was taken to reach it at each step inside a sequence.
     *
     * @param occurrence the elements taken, outermost first. Empty where the position is inside no
     *                   sequence, which is one value and stands with every other
     */
    record At(java.util.Map<souther.compiler.inputs.TermPath, Integer> occurrence, String classId) {

        public At {
            occurrence = java.util.Map.copyOf(occurrence);
        }

        /**
         * Whether this and {@code other} can be one reading of the row.
         *
         * <p>Every step inside a sequence the two took together was taken at the same element, and
         * the steps they did not take together are free. Keyed by the step rather than counted: two
         * positions under one person agree about the person and, where each goes on into a
         * collection of its own, about nothing below it — counted, the two collections would be
         * zipped, which is a relation neither the row nor the model states.
         */
        public boolean agreesWith(At other) {
            for (java.util.Map.Entry<souther.compiler.inputs.TermPath, Integer> each
                    : occurrence.entrySet()) {
                Integer beside = other.occurrence().get(each.getKey());
                if (beside != null && !beside.equals(each.getValue())) {
                    return false;
                }
            }
            return true;
        }
    }

    record Unclassified(Incompleteness reason) implements Classification {

        @Override
        public Incompleteness stopped() {
            return reason;
        }
    }

    static Classification in(String classId) {
        return new Classified(java.util.List.of(new At(java.util.Map.of(), classId)), null);
    }

    /**
     * The same, of a position whose values fell in more than one, each with the elements taken to
     * reach it — and why any of them could not be placed.
     */
    static Classification at(java.util.List<At> at, Incompleteness stopped) {
        return at.isEmpty() && stopped != null ? new Unclassified(stopped)
                : new Classified(at, stopped);
    }

    /**
     * The classes of {@code one} that some value of {@code other} stands with, as a pair.
     *
     * <p>A pair is one value in one class and one value in another, and where the two positions are
     * inside the same sequence it is <em>one element</em> in both. So the pairs a row covers are
     * read by matching the elements the two values came from, as far as the two paths take the same
     * steps inside a sequence — and not by taking every combination of the classes, which counts a
     * row as evidence for a pair none of its elements is in.
     *
     */
    static java.util.List<java.util.Map.Entry<String, String>> pairsOf(
            Classification one, Classification other) {
        if (!(one instanceof Classified left) || !(other instanceof Classified right)) {
            return java.util.List.of();
        }
        java.util.List<java.util.Map.Entry<String, String>> out = new java.util.ArrayList<>();
        for (At each : left.at()) {
            for (At beside : right.at()) {
                if (!each.agreesWith(beside)) {
                    continue;
                }
                java.util.Map.Entry<String, String> pair =
                        java.util.Map.entry(each.classId(), beside.classId());
                if (!out.contains(pair)) {
                    out.add(pair);
                }
            }
        }
        return java.util.List.copyOf(out);
    }

    static Classification unreadable(Incompleteness.Code code, String behavior, String path) {
        return new Unclassified(Incompleteness.atPosition(code, behavior, path));
    }

    default boolean isClassified() {
        return this instanceof Classified;
    }
}
