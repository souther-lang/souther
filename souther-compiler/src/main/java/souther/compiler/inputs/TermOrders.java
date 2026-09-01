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

    private final Carrier observed;
    private final Carrier answered;

    /**
     * @param observed what a value at the term's path is decoded on, or null where nothing orders
     *                 it — a container has no order and is read by what it holds
     * @param answered what the number the term names is measured on, which is what a boundary on it
     *                 is drawn and written back on
     */
    TermOrders(Carrier observed, Carrier answered) {
        this.observed = observed;
        this.answered = answered;
    }

    /** A term whose value is the number it answers, which is every {@link NumericTerm.ValueOf}. */
    static TermOrders itself(Carrier carrier) {
        return new TermOrders(carrier, carrier);
    }

    /** What a value at the term's path is decoded on, or null where nothing orders it. */
    public Carrier observed() {
        return observed;
    }

    /** What the number the term names is measured on. */
    public Carrier answered() {
        return answered;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof TermOrders that
                && java.util.Objects.equals(observed, that.observed)
                && java.util.Objects.equals(answered, that.answered);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(observed, answered);
    }

    @Override
    public String toString() {
        return "TermOrders[observed=" + observed + ", answered=" + answered + "]";
    }
}
