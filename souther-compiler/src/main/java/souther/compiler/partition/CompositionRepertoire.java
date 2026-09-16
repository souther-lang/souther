package souther.compiler.partition;

/**
 * A population this compiler offers some of rather than all of.
 *
 * <p><b>Apart from {@link CompositionBudget}, and the difference is what a reader can do.</b> A
 * figure is a number somebody wrote down: raise it and the search goes on to what it was holding.
 * One of these is a set of values this compiler has no way of producing the rest of — raising
 * anything reaches none of them, and what would is somebody writing the rest. Held in one
 * vocabulary, the two are a set a reader unions and then acts on by raising a number that changes
 * nothing.
 *
 * <p>So neither is the other's default. A walk under a figure that ran out of pieces reached no
 * figure at all, and a walk that went everywhere it knows how to go refused nothing — and both
 * leave an offer that is not the whole of what there is, which is the one thing they have in
 * common and the reason both have to travel.
 *
 * <p><b>Said only where it cannot be shown otherwise.</b> A walk that produced everything of its
 * kind says so, and every other walk is one of these: an offer claiming to be everything is a claim
 * about a population, and the walk that would have to have enumerated it is the only thing that
 * could establish one. So this is what a walk says by default, and completeness is what it has to
 * prove.
 */
public enum CompositionRepertoire {

    /**
     * The ways a difference is spread over the elements of a container adding up to a total.
     *
     * <p>Two are written — the whole of it on as few elements as will carry it, and as near an
     * equal share each as the order allows — and the arrangements of more than one element are
     * many. Which of them a rule tells apart is the rule's own business, so no reading of the two
     * says anything about the rest.
     */
    WAYS_A_TOTAL_IS_SPREAD,

    /**
     * The places on a line between two positions that a pair is tried standing at.
     *
     * <p>Where the order has a smallest step, the places either side of the first one are stepped
     * to and what stops the walk is a figure ({@link CompositionBudget#PLACES_A_PAIR_IS_TRIED_AT}).
     * Where it has none there is no step to take, so the one place the two ranges give up is the
     * whole of what this names — and the line holds every other place it could have named. Raising
     * anything reaches none of them; what would is a way of naming a second place on such an order.
     *
     * <p>Which is why a pair found nowhere there is this and not a proof. Two strings the rules
     * leave a pair for anywhere but at that one place come back with nothing composed, and read as
     * an answer about the rules it says the model refuses a relation it satisfies.
     */
    PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE,

    /**
     * The values that answer several of their own numbers at once.
     *
     * <p>A location asked for two numbers is one value to write, and which values have both is
     * solved for rather than put together. What is written here is the parts a moment is spelled
     * in: the parts of a time and the parts of a date are places in the spelling, so a value with
     * all of them asked for is built by writing each place. Every other group is solved for out of
     * the numbers, and nothing here does that — a whole number whose halves and thirds are both
     * asked for is a value this compiler names none of.
     *
     * <p>So a group nothing built a value for is not a group no value answers. Raising anything
     * reaches none of them; what would is somebody writing the solving.
     */
    VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS,

    /**
     * The places inside one run of an order that this compiler names a value at.
     *
     * <p>It names one. Where the order has a smallest step there are others to step to and nothing
     * here steps to them; where it has none — a decimal, a moment — there is no step to take at
     * all, and the one place the run gives up is the whole of what this compiler can name in it.
     * Raising anything reaches none of the rest, which is what makes this a population and not a
     * figure: what would reach them is a way of naming a second place in a run.
     *
     * <p>So a class whose one named place builds nothing is not a class with no value in it. Read
     * as a figure, an author is told to raise a number that changes nothing; read as an answer
     * about the model, they are told the range holds no value when what happened is that this
     * compiler tried one of them.
     */
    PLACES_IN_A_RUN_THAT_ARE_NAMED
}
