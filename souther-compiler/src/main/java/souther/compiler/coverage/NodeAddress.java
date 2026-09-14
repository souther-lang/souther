package souther.compiler.coverage;

import java.util.Set;

/**
 * Where one place of one body is, said so that two walks of that body come to the same answer.
 *
 * <p><b>Every way to it, not one of them.</b> A body is a tree to read and a graph to walk: a pass
 * that rewrote two equal subtrees into one left a node two ways lead to, and the numbering treats it
 * as one place — it is one comparison, numbered once. So what the place is includes both ways, and
 * an address holding only the first would say the same thing about a body where the second way went
 * somewhere else. Ordinarily there is one way and this holds one path.
 *
 * <p>A set and not a list, because the ways to a place do not come in an order that means anything:
 * which one a walk finds first is the walk's business, and two walks that found them in different
 * orders found the same place.
 *
 * @param behavior whose body the place is in. A path is the same list of slots in every body shaped
 *                 alike, so the path alone is not a place
 * @param occurrences every way down from that body to it
 */
public record NodeAddress(String behavior, Set<CorePath> occurrences) {

    public NodeAddress {
        if (behavior == null) {
            throw new IllegalArgumentException("a place is a place in somebody's body");
        }
        if (occurrences == null || occurrences.isEmpty()) {
            throw new IllegalArgumentException(
                    "a place with no way to it is one nothing reaches: " + behavior);
        }
        occurrences = Set.copyOf(occurrences);
    }

    @Override
    public String toString() {
        return occurrences.size() == 1
                ? behavior + occurrences.iterator().next()
                : behavior + occurrences;
    }
}
