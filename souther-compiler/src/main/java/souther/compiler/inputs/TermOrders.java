package souther.compiler.inputs;

import souther.compiler.check.Carrier;

/**
 * The two orders one term stands on: the one a value of it is observed on, and the one the number it
 * answers is measured on.
 *
 * <p>Two and not one. For a term that is a location's own content they are the same order and there
 * was nothing to tell apart; for a term that is what an operation answered they are the operation's
 * two ends — {@code Date.year(d)} is read off a value counted in days and answers a number counted
 * by one. Held as a single {@code Carrier}, a reader had whichever of the two whoever built it
 * happened to mean, and the one it was not is the one that says nothing when it is wrong: a boundary
 * measured on the argument's order is sharpened onto a value the term never takes, and a row decoded
 * on the answer's order is read as a number the model never named (#1027).
 *
 * <p>Which is the same lesson {@link Carrier} records one size up. Reading a rule and writing a
 * value were two types there while a {@code Time} could be read and not written, and the two agreed
 * with each other and with nothing else. The repair was to hold both ends of one crossing together,
 * and this holds both ends of one term together for the same reason.
 *
 * <p><b>Read anywhere and made in one place.</b> Which orders a term stands on follows from where
 * the reading of an input has that term standing, so a pair put together outside this package is a
 * pair about no reading in particular — and a pair whose halves came from two callers is one whose
 * two ends are free to part. Neither is a class of mistake a reader can see, so neither is a state
 * this lets anything reach: the way to one of these is {@link Quantities#ordersOf}. A test that
 * wants a synthetic pair writes one in this package, where the source set says it is a test.
 */
public final class TermOrders {

    private final NumericTerm term;
    private final Carrier observed;
    private final Carrier answered;

    /**
     * @param term     the number these are the orders of. Carried, because an answer that leaves
     *                 the reading and cannot say what it is an answer about is one any reader may
     *                 put beside any term — and two carriers say nothing about which question they
     *                 came from
     * @param observed what a value at the term's path is decoded on, or null where nothing orders
     *                 it — a container has no order and is read by what it holds
     * @param answered what the number the term names is measured on, which is what a boundary on it
     *                 is drawn and written back on
     */
    TermOrders(NumericTerm term, Carrier observed, Carrier answered) {
        if (term == null) {
            throw new IllegalArgumentException("orders of no term, which is an answer to nothing");
        }
        this.term = term;
        this.observed = observed;
        this.answered = answered;
    }

    /** The number these are the orders of. */
    public NumericTerm term() {
        return term;
    }

    /**
     * That {@code asked} is the number these are the orders of.
     *
     * <p>For the readers that hold a term beside a pair because their own shape needs the narrower
     * type. Two components are two things to get right, and this is where the second is refused
     * rather than carried into a document.
     */
    public void areOf(NumericTerm asked) {
        if (!term.equals(asked)) {
            throw new IllegalArgumentException("these are the orders of " + term
                    + ", and they are held beside " + asked);
        }
    }

    /**
     * The number this term names at {@code value}, or why there is none.
     *
     * <p>Asked of the answer and not of the term, because reading takes both and an entry taking
     * both is one any caller can hand a term and another term's orders. Here the two arrived
     * together from the reading that settled them.
     */
    public NumericTerm.Reading read(souther.compiler.observe.ObservedValue value) {
        if (term.atOnePosition() == null) {
            throw new IllegalArgumentException(
                    term + " is read over the values of a run, and this is one value");
        }
        return TermReading.at(this, value);
    }

    /**
     * The same, over the values of a run.
     *
     * <p>Which rows there are and how many values stand at a place in one are the measure's; a term
     * only says what its number is of them.
     */
    public NumericTerm.Reading readOver(java.util.List<souther.compiler.observe.ObservedValue> values) {
        if (!(term instanceof NumericTerm.TakenOver)) {
            throw new IllegalArgumentException(term + " is a number of one value, not of a run");
        }
        return TermReading.over(this, values);
    }

    /** What a value at the term's path is decoded on, or null where nothing orders it. */
    public Carrier observed() {
        return observed;
    }

    /** What the number the term names is measured on. */
    public Carrier answered() {
        return answered;
    }

    /**
     * Two of these are one where they are the orders of one term.
     *
     * <p>The term among them, because these are an answer and not a pair of carriers: what a string
     * is measured at and what a whole number at another position is measured at come to the same two
     * orders and are answers to two questions. A reader that wants the carriers alone compares
     * those.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof TermOrders that
                && term.equals(that.term)
                && java.util.Objects.equals(observed, that.observed)
                && java.util.Objects.equals(answered, that.answered);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(term, observed, answered);
    }

    @Override
    public String toString() {
        return "TermOrders[" + term + " observed=" + observed + ", answered=" + answered + "]";
    }
}
