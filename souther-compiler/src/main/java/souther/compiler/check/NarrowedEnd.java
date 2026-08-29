package souther.compiler.check;

import souther.compiler.numeric.Endpoint;

/**
 * One end of what a reading leaves a position, and the declarations holding it.
 *
 * <p>One of these exists only where there is an end. A side the rules leave everything has no end
 * for anybody to hold, so it has none of these — which is what turns "an absent end is nobody's"
 * from a check made when the value is built into a statement about which values there are.
 *
 * <p>Which of the two ends this is, is not held here. It is which field of a {@link
 * NarrowedBounds.Reading} the end sits in, and stating it here as well would be the same fact
 * written twice, with a value able to say it is the lower end while sitting in the upper one.
 */
final class NarrowedEnd {

    private final Endpoint endpoint;
    private final Held held;

    NarrowedEnd(Endpoint endpoint, Held held) {
        if (endpoint == null) {
            throw new IllegalArgumentException("an end a reading leaves is somewhere");
        }
        this.endpoint = endpoint;
        this.held = held;
    }

    Endpoint endpoint() {
        return endpoint;
    }

    Held held() {
        return held;
    }
}
