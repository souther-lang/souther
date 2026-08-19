package souther.compiler.partition;

/**
 * Which way along an order something runs from where it starts.
 *
 * <p>Shared rather than owned by any one of the things that needs it. A side of a border runs one
 * way ({@link Criterion.Beyond}), the value beside a line lies one way
 * ({@link LevelSpace#neighbour}), and a rule is satisfied one way of its threshold — three readers
 * of one word, and it belonged to the first of them to be written while the other two named it
 * through that one.
 */
public enum Towards {
    ABOVE,
    BELOW;

    /** The other way. */
    public Towards opposite() {
        return this == ABOVE ? BELOW : ABOVE;
    }
}
