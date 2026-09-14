package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Places a search is not to offer, and the answer to whether a place is one of them.
 *
 * <p><b>The question travels with the places.</b> Whether a candidate is one of these is asked on
 * the order and never on the spelling: {@code 0.00} and {@code 0} are one place, and a list of them
 * answers {@code contains} by how each was written ({@link Place#key}). Handed round as a list,
 * every caller decides that for itself — and a caller that decided it by equality offered a place
 * the search had already tried and come back from, which a figure counting the values a search has
 * tried spends on nothing.
 *
 * <p>One entry per place. What a walk over a run spends is a step for each value it was told to
 * keep away from, so two spellings of one place counted twice would buy a step that rules nothing
 * further out.
 */
public record PlacesApart(List<Place> places) {

    /** Nothing is held apart, which is where a search that has tried nothing starts. */
    public static final PlacesApart NONE = new PlacesApart(List.of());

    public PlacesApart {
        List<Place> kept = new ArrayList<>();
        for (Place each : places) {
            if (each != null && kept.stream().noneMatch(each::sameAs)) {
                kept.add(each);
            }
        }
        places = List.copyOf(kept);
    }

    /** These places, as they were written. */
    public static PlacesApart of(Collection<Place> places) {
        return places.isEmpty() ? NONE : new PlacesApart(List.copyOf(places));
    }

    /** Whether {@code at} is one of these, which is a question about the order. */
    public boolean has(Place at) {
        return at != null && places.stream().anyMatch(at::sameAs);
    }

    /** Whether nothing is held apart. */
    public boolean isEmpty() {
        return places.isEmpty();
    }

    /** How many places these are, which is how many a walk has to get past. */
    public int count() {
        return places.size();
    }
}
