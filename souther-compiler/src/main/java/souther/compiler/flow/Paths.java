package souther.compiler.flow;

import java.util.List;

/**
 * The ways to a value, where the naming could hold them apart.
 *
 * <p>The half of a reading that the naming has anything to do with. What a body does is answered
 * beside this and never out of it: a naming that has no words for a condition, that sees two
 * conditions settle one decision opposite ways, or that is asked to hold more ways apart than it
 * will — each of those leaves this saying less, and none of them may leave the reading of what
 * arrives or of what a value comes to saying anything different.
 *
 * <p>So {@link Beyond} is the only degradation there is, and it is an answer about this list rather
 * than about the body: these ways are not something this reading will enumerate. A reader wanting to
 * steer a run down one of them has nothing here; a reader asking whether a value arrives was never
 * asking this.
 */
public sealed interface Paths<P> {

    /**
     * These ways and no others.
     *
     * <p>Empty exactly where no run arrives at a value. A list emptied by the naming having seen that
     * no run takes any of these is not this — it is {@link Beyond}, because the body still arrives
     * and a list saying otherwise would be the naming answering a question that is not its.
     */
    record Held<P>(List<Arrival<P>> arrivals) implements Paths<P> {

        public Held {
            arrivals = List.copyOf(arrivals);
        }
    }

    /** Which ways there are is not something this reading will hold apart. */
    record Beyond<P>() implements Paths<P> { }

    /** The ways, or none where this reading will not hold them apart. */
    default List<Arrival<P>> orNone() {
        return this instanceof Held<P> held ? held.arrivals() : List.of();
    }
}
