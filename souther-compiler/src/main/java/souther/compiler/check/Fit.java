package souther.compiler.check;

import souther.compiler.types.Type;

/**
 * What a solving walk makes of one type read against another: they fit, or two positions disagree.
 *
 * <p>A walk knows which two types did not go together. It does not know which operand supplied
 * either of them, where that operand is written, or what a reader should be told — those are the
 * elaborator's, which still has the expression in hand when it asks. A walk that answered with a
 * report instead would have to be given a position and a sentence before the answer was known, and
 * every caller that only wanted to know whether the types fit would assemble both and throw them
 * away.
 *
 * <p>So the answer carries the types and nothing else, and the diagnostic is chosen from it by
 * whoever owns the operand — the same shape {@link ArithmeticCheck} takes for the same reason.
 */
sealed interface Fit {

    /** The one answer that says nothing further, so it is one value rather than one per walk. */
    Fit FITS = new Fits();

    /** {@code arg} is admissible where {@code param} was written, and what it settled stands. */
    record Fits() implements Fit {}

    /**
     * {@code expected} was already stated at this position — by the declaration, or by an earlier
     * reading of the variable standing there — and {@code actual} does not go with it.
     *
     * <p>Both are written in the caller's terms rather than the walk's: they are the types a reader
     * would be shown, at the position that disagreed, not the outermost pair the walk started from.
     */
    record Disagrees(Type expected, Type actual) implements Fit {}
}
