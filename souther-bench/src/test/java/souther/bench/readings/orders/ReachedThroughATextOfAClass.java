package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;

import java.util.Set;

/**
 * A reader handed nothing, which meets a copy only in the text of an object it made.
 *
 * <p>Each makes the object of a set that came out of no copy and reads none of its fields; the text
 * it asks for says them all, and the one the object's constructor copied is said in the order the
 * run gave it. One joins the object into a text, which this compiler writes as a call that takes
 * any object; the other asks the object for its text by name.
 *
 * <p>And one is handed the object by nothing in the program: what it says of it is still what the
 * class's fields hold.
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
        return "kept: " + new Kept(Set.of());
    }

    public static String saidOfOneItIsHanded(Kept kept) {
        return "kept: " + kept;
    }

    public static String saidByItsOwnText() {
        return new Kept(Set.of()).toString();
    }
}
