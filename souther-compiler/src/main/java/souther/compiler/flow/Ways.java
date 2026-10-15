package souther.compiler.flow;

import java.util.List;

/**
 * The ways a value is settled to one truth, or that this reading cannot enumerate them.
 *
 * <p>All of them or none of them, and the type is what holds it to that. A list with ways missing
 * from it reads as a whole one: whatever takes it steers no run down the ways it does not hold, so
 * one way this reading could not write down whole makes the enumeration {@link Unknown} rather than
 * quietly leaving itself out of a {@link Known} one.
 *
 * <p>{@code Known} holding nothing is an answer and not an absence. It says the value is never
 * settled that way, which is how an arm no run reaches is told from an arm this reading has nothing
 * to say about.
 */
public sealed interface Ways<P> {

    /**
     * These ways to that truth, and no others.
     *
     * @param seenApart whether what a run is seen doing tells each of them from every other
     *                  ({@link Naming#toldApart}). Every way here holds what it says, and where this
     *                  is false a run seen on one may have been on another: what the ways say is
     *                  what a run read, and is no account of which one it took
     */
    record Known<P>(List<P> paths, boolean seenApart) implements Ways<P> {

        public Known {
            paths = List.copyOf(paths);
        }
    }

    /** Which ways come to that truth is not something this reading can say. */
    record Unknown<P>() implements Ways<P> { }
}
