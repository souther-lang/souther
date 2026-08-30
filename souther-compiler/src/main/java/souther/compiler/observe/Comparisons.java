package souther.compiler.observe;

/**
 * The one comparison, for the two faces that are bound to a reading of the declarations.
 *
 * <p>Whether an answer is what a text stated is the language's to settle, and settling it takes
 * what the declarations say stands inside a value. Whoever supplies that decides part of the
 * answer — a field declared a set is compared without its order, and one nothing declares is
 * compared in the order it stands — so where the reading comes from is what makes a verdict the
 * language's rather than the reader's.
 *
 * <p>Which is why this is not reachable from a statement. A comparison hanging off what a row
 * states is one a reader can make with declarations of its own, and two readings of one row would
 * answer differently about one answer. The faces that ask are bound where they are made: the
 * compile asks with the declarations it read the text against, and a checked program's row asks
 * with the ones that program publishes.
 */
public final class Comparisons {

    private Comparisons() {}

    /**
     * Whether {@code answered} keeps what {@code stated} states, read with {@code types} and at
     * {@code answers}.
     *
     * <p>For whoever holds a reading of the declarations to bind to. What is answered here is the
     * same for both faces, which is what makes a row mean one thing wherever it is read.
     */
    public static Verdict verdict(Expectation stated, ObservedValue answered, ValueTypes types,
                                  Position answers) {
        if (stated == null || answered == null || types == null || answers == null) {
            throw new IllegalArgumentException("a comparison is of a statement against an answer,"
                    + " read with what the declarations say and where the answer stands");
        }
        return new ValueMatch(types).verdict(stated, answered, answers);
    }
}
