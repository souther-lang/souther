package souther.compiler.partition;

import java.util.function.IntSupplier;

/**
 * How much of a search this compiler is willing to do before it stops.
 *
 * <p>One member per place that stops, and the figure it stops at is here rather than at the place.
 * What a reader of a stopped search wants to know is which of these ran out, and a name written
 * beside a number somewhere else is a second declaration of the same policy — the two part the
 * first time one of them is raised.
 *
 * <p><b>A cause and not an outcome.</b> Reaching one of these says what this compiler declined to
 * do and says nothing about the model: the value it did not build may be the easiest one in the
 * file to write by hand. What the reaching did to the answer is a separate question, and it has two
 * answers rather than one — a search that had produced nothing when it stopped leaves the point
 * unestablished, and one that had produced something leaves an offer that is some of what there was.
 * So the same member appears on both sides and is neither of them.
 *
 * <p>The figures are read through {@link #maximum()} and are not all written down. One of them is
 * how many shapes a decomposition is offered in, which is how many the walk has — read off the walk,
 * so that a shape added there is a budget raised here and not a number that stayed behind.
 */
public enum CompositionBudget {

    /** How many elements a proposed collection is worth building. A row is offered for somebody to
     *  read and complete, and a minimum past this asks for one nobody would. */
    ELEMENTS_A_PROPOSAL_HOLDS(() -> 64),

    /** How many characters a proposed string is worth building. Its own figure, because a string of
     *  sixty-five is one literal where a collection of sixty-five is sixty-five values each built in
     *  turn — holding the two to one number bounds a string by something about collections. */
    CHARACTERS_A_PROPOSAL_HOLDS(() -> 4096),

    /** How many pairings of what a map's key and value propose are built at once. Every pair is
     *  built before any of them is tried, so this bounds what is allocated rather than what is
     *  walked. */
    PAIRINGS_BUILT_AT_ONCE(() -> 64),

    /** How many elements a container built to reach a total is worth carrying. Its own figure and
     *  not {@link #ELEMENTS_A_PROPOSAL_HOLDS}, though they agree: held as one, a change made for one
     *  of them would move the other for no reason anybody could state. */
    ELEMENTS_A_TOTAL_IS_SPREAD_OVER(() -> 64),

    /** How many containers are offered for one total. They are alike to the total, so what a fifth
     *  buys is another row reading like the last. */
    SHAPES_OF_A_TOTAL_OFFERED(() -> 4),

    /** How many ways the difference between a starting point and a total is spread over the
     *  elements. Read off the walk that has them, so a third way of spreading is this budget
     *  raised. */
    DECOMPOSITIONS_OF_A_TOTAL_OFFERED(ContainersAddingUp::decompositionsOffered),

    /** How many places along a line a pair is tried at. What a range cannot say is that one of its
     *  values is missing, so what stepping past this walks over is holes, and there are as many of
     *  those as the rules state. */
    PLACES_A_PAIR_IS_TRIED_AT(() -> 64),

    /** How many steps a walk over the positions of a form may take. A run without an end is not
     *  walked to the end at any length. */
    STEPS_A_SEARCH_MAY_TAKE(() -> 200_000),

    /** How many assignments of one parameter's positions a search composes. A bound on the search
     *  and not on any one position. */
    ASSIGNMENTS_A_SEARCH_COMPOSES(() -> 256);

    private final IntSupplier maximum;

    CompositionBudget(IntSupplier maximum) {
        this.maximum = maximum;
    }

    /** The figure this stops at. */
    public int maximum() {
        return maximum.getAsInt();
    }
}
