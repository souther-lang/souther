package souther.compiler.observe;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * Which element was taken from each container on the way to one value, outermost first.
 *
 * <p>The element and not only the value, because a relation between two positions is about one
 * element and not about the two sets: one person under a line and another over it are two readings
 * of a row, and which went with which is the whole of what a pair of positions says. Empty where the
 * position is inside no container, which is one value and stands with every other.
 *
 * <p><b>Keyed by the container, and not by the part of it a position is at.</b> A map's key and the
 * value filed under it are two positions, and the entry is one: the key of the first entry and the
 * value of the second were never written together, and a row read as though they were stands at a
 * point no entry is at. So a key and a value taken from one map are taken at the map, and each says
 * which entry; what a list holds is taken at the list the same way.
 *
 * <p><b>In the order the containers were entered.</b> The containers one value was reached through
 * run from the outermost to the innermost, and that order is part of what this holds. What a reader
 * builds from them — the readings of a row over its containers, tried up to a bound — depends on
 * it, so it is kept as written rather than left to whatever order a map hands its keys back in.
 *
 * <p>Asked whether two values can be one reading of the row ({@link #agreesWith}) and what element
 * was taken from a container ({@link #elementAt}); nothing here hands the containers over as a map
 * to be walked in whatever order it comes.
 *
 * @param outermostFirst the containers entered, each with the element taken from it
 */
public record ElementsTaken(List<Taken> outermostFirst) {

    /** Nothing taken: the position is inside no container. */
    public static final ElementsTaken NONE = new ElementsTaken(List.of());

    /** One container entered and the element taken from it. */
    public record Taken(TermPath container, int element) {

        public Taken {
            Objects.requireNonNull(container, "an element is taken from a container");
        }
    }

    /**
     * A container is entered once. Two elements of one container would be two readings of the row
     * in one value, and {@link #agreesWith} — which asks each container of one against the other —
     * would answer differently from either side.
     */
    public ElementsTaken {
        outermostFirst = List.copyOf(outermostFirst);
        Set<TermPath> seen = new HashSet<>();
        for (Taken each : outermostFirst) {
            if (!seen.add(each.container())) {
                throw new IllegalArgumentException(
                        "a container is entered once: " + each.container());
            }
        }
    }

    /** These, and one element more taken from {@code container}, inside them. */
    public ElementsTaken and(TermPath container, int element) {
        List<Taken> deeper = new ArrayList<>(outermostFirst);
        deeper.add(new Taken(container, element));
        return new ElementsTaken(deeper);
    }

    /** The element taken from {@code container}, or null where this entered no such container. */
    public Integer elementAt(TermPath container) {
        for (Taken each : outermostFirst) {
            if (each.container().equals(container)) {
                return each.element();
            }
        }
        return null;
    }

    /**
     * Whether this and {@code other} can be one reading of the row.
     *
     * <p>Every container the two entered together was entered at the same element, and the ones they
     * did not enter together are free. Keyed by the container rather than counted, so the rule is one
     * sentence and every case follows from it: two positions under one person agree about the
     * person; a zip code and a phone number under one person agree about the person and not about
     * the address or the phone; a map's key and a value agree about the entry; two positions under
     * different parameters share nothing and stand with each other however they are spelled; and a
     * position inside no container enters none, so it stands with everything.
     *
     * <p>Counted instead — the first so many elements of one list against the first so many of
     * another — two sibling collections would be zipped, which is a relation neither the row nor the
     * model states.
     */
    public boolean agreesWith(ElementsTaken other) {
        for (Taken each : outermostFirst) {
            Integer beside = other.elementAt(each.container());
            if (beside != null && beside != each.element()) {
                return false;
            }
        }
        return true;
    }
}
