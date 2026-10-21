package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;

import java.util.Set;

/**
 * A reader handed nothing, which meets a copy only in the text of an object it made.
 *
 * <p>It makes the object of a set that came out of no copy and reads none of its fields; the text
 * it asks for says them all, and the one the object's constructor copied is said in the order the
 * run gave it.
 */
public final class ReachedThroughATextOfAClass {

    private ReachedThroughATextOfAClass() {}

    /**
     * What a copy made, held in a field of a record whose text says it.
     *
     * @param figures a set of the figures a search is held to
     */
    public record Kept(Set<CompositionBudget> figures) {

        public Kept {
            figures = Set.copyOf(figures);
        }
    }

    public static String said() {
        return new Kept(Set.of()).toString();
    }
}
