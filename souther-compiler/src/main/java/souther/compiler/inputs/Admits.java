package souther.compiler.inputs;

/**
 * What the declarations reaching a position say about one distinction standing there.
 *
 * <p>Three answers and not two, because the two that read alike are the ones a measure must not
 * run together. A distinction the rules refuse is one no row can be written at; a distinction the
 * rules leave is one a caller can supply; and a distinction the reading could not settle is neither,
 * and saying so is the only honest thing to do with it.
 *
 * <p>The asymmetry between the last two is the whole of what makes this sound. A refusal is proven
 * whether or not the reading ran to the end — what the rules leave is an upper bound in every
 * reading, so a distinction that bound leaves nothing is one the position cannot hold — while an
 * admission is proven only where every rule was taken in, since a rule that went unread can refuse
 * as readily as one that was read.
 */
public sealed interface Admits {

    /**
     * Every rule reaching the position was read, and they leave this distinction a value.
     *
     * <p>Which is what a caller can supply, and so what refutes a body declaring the case cannot
     * arrive.
     */
    record Admitted() implements Admits {}

    /** The rules leave this distinction nothing, so no value of it stands here and no row can be
     *  written at it. */
    record Refused() implements Admits {}

    /**
     * The declarations did not settle it.
     *
     * <p>Carries which of the two ways that happened ({@link Unsettlement}), because the answer is
     * about this compiler rather than about the model and a reader has to be able to say which.
     * Nothing follows about whether a value of the distinction can stand here.
     */
    record Unsettled(Unsettlement why) implements Admits {

        public Unsettled {
            if (why == null) {
                throw new IllegalArgumentException(
                        "a reading unsettled by nothing is one that settled it");
            }
        }
    }
}
