package souther.compiler.flow;

/**
 * What a naming writes one of the ways into an arm as.
 *
 * <p>Three answers and not a path or null, because the two ways of not writing one down are two
 * different news. A way this naming has no words for is still a way, and a list of the ways without
 * it reads as all of them; a way that settles one decision two ways is no run at all, and leaving it
 * out is the list being whole.
 */
public sealed interface WayWritten<P> {

    /** The way, written down whole. */
    record As<P>(P path) implements WayWritten<P> {

        public As {
            if (path == null) {
                throw new IllegalArgumentException("a way written down is written as something");
            }
        }
    }

    /** A way this naming has no words for. */
    record NoWords<P>() implements WayWritten<P> { }

    /** A way no run takes: what it says settles one decision two ways. */
    record NoRun<P>() implements WayWritten<P> { }
}
