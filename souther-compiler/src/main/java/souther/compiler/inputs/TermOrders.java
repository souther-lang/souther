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
 * @param observed what a value at the term's path is decoded on, or null where nothing orders it —
 *                 a container has no order and is read by what it holds
 * @param answered what the number the term names is measured on, which is what a boundary on it is
 *                 drawn and written back on
 */
public record TermOrders(Carrier observed, Carrier answered) {

    /** A term whose value is the number it answers, which is every {@link NumericTerm.ValueOf}. */
    public static TermOrders itself(Carrier carrier) {
        return new TermOrders(carrier, carrier);
    }
}
