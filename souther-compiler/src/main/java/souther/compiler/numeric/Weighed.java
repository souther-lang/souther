package souther.compiler.numeric;

import java.util.Map;

/**
 * What a form weighs, which never changes, and what was last worked out of it over the coordinates
 * of a basis.
 *
 * <p>The weights are copied in, so that what a basis kept of a form is what the form says whoever
 * holds the map it was made from. A form is asked of one domain after another, each with a basis
 * of its own, and the weights over a basis's coordinates are the same for every basis that has the
 * same places ({@link PrefixBasis}); keeping them with the form is keeping them where they are
 * asked, and for as long as the form is.
 *
 * @param <A> what a position is
 */
final class Weighed<A> {

    private final Map<A, ExactRatio> coefs;

    /** What the last basis that was asked worked out, or null; replaced whole, and never changed. */
    private volatile PrefixBasis.Prepared prepared;

    private Weighed(Map<A, ExactRatio> coefs) {
        this.coefs = coefs;
    }

    /** The weights {@code coefs} say, held apart from the map they came in. */
    static <A> Weighed<A> of(Map<A, ExactRatio> coefs) {
        return new Weighed<>(Map.copyOf(coefs));
    }

    /** The weights, which no one changes. */
    Map<A, ExactRatio> coefs() {
        return coefs;
    }

    PrefixBasis.Prepared prepared() {
        return prepared;
    }

    void prepared(PrefixBasis.Prepared now) {
        prepared = now;
    }
}
