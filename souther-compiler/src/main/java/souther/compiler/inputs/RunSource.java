package souther.compiler.inputs;

/**
 * Where the values an operation walked came from, for a number taken over a run of them.
 *
 * <p>A model writes {@code List.sum(List.map(f, xs))} and means the numbers at a place inside
 * {@code xs} added up. There is no position holding that list — the walk that made it is gone from
 * the tree by the time anything measures, and the list never stood anywhere a row writes — so what
 * such a number is taken of is said as where its values came from rather than as a location.
 *
 * <p><b>What is claimed is the values and their number, and nothing about their order.</b> As many
 * values as stand at the place named, each of them one of them: that is what a sum needs, since a
 * total does not depend on which came first. An operation that does depend on it — a first, a
 * running total, anything read by index — is not entitled to rest on this, and would need something
 * that says the walk kept the order as well.
 *
 * <p>Beside {@link TermPath} and not a kind of one. A path says where a location is and says
 * nothing about how many values stand there, deliberately: a rule written about a location and a
 * row walked to it meet by being written the same way, and a multiplicity in the path would make
 * two spellings of one location. So how many values a number is taken of is said here, by the term
 * that takes it.
 */
public sealed interface RunSource {

    /** Where the values are read from. */
    TermPath subjectPath();

    /**
     * The values standing at one position, each element of the walk being one of them.
     *
     * <p>What has to be shown before one of these is made: as many values as the position has, and
     * each of the walk's elements the value at one of them. A construction that keeps some of what
     * it was given, or that answers one element for two, is not this — the numbers added up would
     * be a subset or a multiset of what the row holds, and a rule about the total would be measured
     * against something the model does not state.
     */
    record ProjectedOccurrences(TermPath subjectPath) implements RunSource {

        public ProjectedOccurrences {
            java.util.Objects.requireNonNull(subjectPath, "a run is read from somewhere");
            if (!subjectPath.insideASequence()) {
                throw new IllegalArgumentException(
                        "a run stands inside a sequence, and `" + subjectPath + "` is one position"
                                + " holding one value");
            }
        }

        @Override
        public String toString() {
            return subjectPath.toString();
        }
    }
}
