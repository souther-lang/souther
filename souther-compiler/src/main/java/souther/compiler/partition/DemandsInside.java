package souther.compiler.partition;

import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What a value written whole at one location is asked to hold at positions inside it.
 *
 * <p>A location written whole and a position inside it are one value asked for twice, and what
 * answers both is a value composed to hold both — so a caller that has a number for the location
 * and values for positions under it hands the second here, to whatever composes the first, rather
 * than writing the two side by side and having them refused as two writes at one place.
 *
 * <p>The two vocabularies a plan is made in, kept apart. A value at a position is what stands
 * there; a narrowing is which case a position is, and says nothing about what stands under it. Put
 * in one map, a case would be a value nothing writes, and {@link ConstructionPlan} is where the two
 * are put together.
 *
 * <p><b>The values a position may stand at, and not one of them.</b> A class stands for its values
 * through as many of them as it offers, because the first can be refused beside the rest of a row
 * where another of the class's own is not; a position asked for by a class is asked for any of
 * them, and what composes the location tries them. A value asked for exactly is the one value of
 * its list — the same arrangement {@link LocationWrites} holds a location's values in.
 *
 * <p>Positions of every element alike. A position under {@code [*]} names no element in
 * particular, so what is asked of it is asked of each element the value holds.
 *
 * @param among    the values each position inside the location may stand at, any one of which
 *                 answers what was asked of it, nearest what was asked first; positions in the
 *                 order they were asked for
 * @param required the narrowings that hold inside the location
 */
record DemandsInside(Map<TermPath, List<FixtureTemplate>> among, Requirements required) {

    /** Nothing asked inside: the location is composed as its own type composes it. */
    static final DemandsInside NOTHING = new DemandsInside(Map.of(), Requirements.NONE);

    DemandsInside {
        Map<TermPath, List<FixtureTemplate>> kept = new LinkedHashMap<>();
        among.forEach((path, values) -> {
            if (values.isEmpty()) {
                throw new IllegalArgumentException("a position asked for is asked for a value: "
                        + path);
            }
            kept.put(path, List.copyOf(values));
        });
        among = Collections.unmodifiableMap(kept);
    }

    /** Whether anything is asked inside at all. */
    boolean isEmpty() {
        return among.isEmpty() && required.refinements().isEmpty();
    }

    /**
     * Two things asked here that no one element holds together, or empty where everything asked
     * can be one element.
     *
     * <p>A position asked for a value names the cases above it that it is under
     * ({@link TermPath#requirements}), and those have to stand beside the narrowings asked for. Where
     * they do not, what was asked contradicts itself — which is a fact about what was asked and not
     * about any one way of building the element, so it is settled here, before any way is tried, and
     * never met halfway down one.
     */
    Optional<Requirements.Merge.Conflict> contradiction() {
        Requirements all = required;
        for (TermPath each : among.keySet()) {
            switch (all.merge(each.requirements())) {
                case Requirements.Merge.Merged(Requirements both) -> all = both;
                case Requirements.Merge.Conflict conflict -> {
                    return Optional.of(conflict);
                }
            }
        }
        return Optional.empty();
    }
}
