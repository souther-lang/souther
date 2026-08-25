package souther.compiler.query;

/**
 * Which readings a generation was asked about.
 *
 * <p>A line an {@code invariant} drew is owed once over every behavior carrying the type, and a row
 * at it is composed by walking one behavior's inputs — so which reading composes the one row the
 * line is owed is a search over the readings. What that search is allowed to walk is this, and it is
 * a question rather than an optimisation: a run asked about one behavior and a run asked about the
 * module are asking different things, and "the first reading that composed a row" means the first of
 * what was asked about.
 *
 * <p><b>Said, and never read off what a search has already answered.</b> A walk over the readings
 * some earlier caller happened to have paid for is a walk whose answer moves with the order the
 * requests arrived in. This is what a request states about itself, before anything is asked.
 *
 * <p>Nothing here decides how much of the evidence a conclusion needs. Whether the readings that
 * were walked are all the readings there are is {@link SearchCoverage}'s to say, and a rule written
 * on the shape of the request — this scope may claim the model settles a point and that one may not
 * — would be false for a line only one behavior carries, which one behavior's walk covers entirely.
 */
public sealed interface GenerationScope {

    /** Whether a reading of a line is one this request searches. */
    boolean admits(String behavior);

    /** Every reading, for a caller printing a block for the module. */
    record Module() implements GenerationScope {

        @Override
        public boolean admits(String behavior) {
            return true;
        }
    }

    /**
     * The readings one behavior makes, for a caller whose question is about that behavior.
     *
     * <p>What an editor offering to write the rows beside a behavior asks. A row composed at another
     * reading is written in that behavior's terms and belongs in that behavior's block, so it is not
     * an answer to this question however well it settles the line.
     */
    record Behavior(String name) implements GenerationScope {

        public Behavior {
            if (name == null) {
                throw new IllegalArgumentException("a scope of one behavior is some behavior's");
            }
        }

        @Override
        public boolean admits(String behavior) {
            return name.equals(behavior);
        }
    }
}
