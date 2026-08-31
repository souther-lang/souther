package souther.compiler.inputs;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

/**
 * What is known of the names in a tree, as facts and with nothing made of them.
 *
 * <p>Two readings are built out of these and they are not the same reading. What a name stands for
 * ({@link ReadMeaning}) is one, and which position of the input an expression reaches
 * ({@link InputPath}) is the other; the first is written in terms of the second, and both are
 * written in terms of what is here. Between them there is one order to read these facts in, and it
 * belongs to whichever reading a caller asked for.
 *
 * <p><b>Facts and never an answer.</b> A reading held here would be reachable from the reading built
 * on it, and the two would call each other: what a name means is worked out by asking which position
 * it reaches, so a walk after a position that could ask what a name means would be asking a question
 * whose answer it is. Kept to facts, that is not something a caller can write.
 *
 * <p>Which is also what keeps a traversal from measuring itself against the environment. How many
 * names are known here is not how far a value's provenance runs — a name bound in one arm is read
 * under bindings written elsewhere — and there is nothing to count with: what stops a walk over
 * these facts is where it has been ({@link BindingTrail}), never how much there is.
 */
public interface BindingEnvironment {

    /** The position {@code binding} is the name of, or null where it names none. */
    TermPath rootOf(BindingId binding);

    /** What {@code binding} holds where this reading has got to, or null where it holds nothing
     *  here. */
    Core boundValueOf(BindingId binding);

    /**
     * The same over the whole body rather than down the way to here, or null where nothing bound it.
     *
     * <p>Beside {@link #boundValueOf} and not a wider version of it. A container built by one
     * operation and handed to the next is bound beside the closure that reads it rather than above
     * it, so the way to it is not the way here — which is a thing to reach for when the question is
     * where a container's elements are, and not when it is what a name stands for.
     */
    Core heldAnywhereBy(BindingId binding);

    /** The container an operation handed {@code binding} an element of, or null where none did. */
    Core containerOf(BindingId binding);

    /** The binding whose elements {@code binding}'s are, or null where none is recorded. */
    BindingId sameElementsAs(BindingId binding);

    /** The binding {@code binding}'s elements were made from, or null where none is recorded. */
    BindingId madeFrom(BindingId binding);

    /**
     * Whether an operation the language defines the meaning of is left standing in this tree.
     *
     * <p>It is in the representation a declaration's own rules are read in and it is not in the one
     * that runs. A call left standing names no location, which is an answer where such a tree is
     * what was handed over and a fault in the caller where it is not.
     */
    boolean callsStand();
}
