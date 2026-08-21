package souther.compiler.coverage;

import souther.compiler.core.Core;
import souther.compiler.flow.Anonymous;
import souther.compiler.flow.AnonymousPath;
import souther.compiler.flow.ValueArrivals;

/**
 * Whether evaluating an expression can answer a value.
 *
 * <p>An {@code unreachable} answers none and aborts instead, and an expression that has to evaluate
 * one on its way answers none either. This is what tells an arm the rows can be in from an arm that
 * only states a combination the model rules out — the first is a fork a row takes, the second is not
 * an arm at all.
 *
 * <p>A projection of {@link ValueArrivals} and not a reading of its own. Whether a value arrives and
 * what it comes to are one question wherever an operator stops as soon as its answer is settled:
 * {@code a > 1 && unreachable} arrives for every small {@code a} and never for a large one, and
 * nothing reading only the shape of the node can say which. So there is one reading, and this is that
 * reading asked whether there is any way at all.
 *
 * <p>Read off the tree and not off the types. An {@code unreachable} is written as {@code Never}, but
 * the position it stands in usually states a shape, and that shape is what the elaborator records on
 * the node — so a {@code match} arm answering {@code unreachable} carries the type of what its
 * siblings answer. The node kind is what survives.
 *
 * <p>What a call answers is not looked into. A non-recursive helper is inlined into the body that uses
 * it, so its arms are already here; a recursive one is a shared method, and a helper that never
 * returns leaves the arm that calls it counted. The arguments are looked at, because they are
 * evaluated before the call is — but a function passed as one is made and not run, so what its body
 * does when the call gets round to it is the call's business and stays unread.
 */
public final class NormalReturn {

    private final ValueArrivals<AnonymousPath> reading;

    private NormalReturn(ValueArrivals<AnonymousPath> reading) {
        this.reading = reading;
    }

    /**
     * The reading of one body, which every question about a node in it is asked of.
     *
     * <p>Rooted, because what a name reads is not a fact about the node that reads it. A
     * {@code Core.Read} standing under a {@code let} that bound it to a number written out is settled
     * by that number; the same node standing in a body that binds nothing is a position of the input.
     * Asking about a subtree on its own would answer the second of those about the first.
     */
    public static NormalReturn ofBody(Core body) {
        return new NormalReturn(ValueArrivals.ofBody(body, Anonymous.NAMING));
    }

    /** Whether {@code e}, standing where it stands in this body, can be evaluated to a value. */
    public boolean at(Core e) {
        return reading.arrivesAt(e);
    }

    /**
     * Whether {@code e} can be evaluated to a value, read as a body of its own.
     *
     * <p>For a caller that has an expression and nothing above it. Every name in it is free, which is
     * what it means for nothing to have bound them.
     */
    public static boolean of(Core e) {
        return ofBody(e).at(e);
    }
}
