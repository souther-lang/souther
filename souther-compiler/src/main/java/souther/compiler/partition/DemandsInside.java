package souther.compiler.partition;

import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What a value written whole at one location is asked to hold at positions inside it.
 *
 * <p>A location written whole and a position inside it are one value asked for twice, and what
 * answers both is a value composed to hold both — so a caller that has a number for the location
 * and values for positions under it hands the second here, to whatever composes the first, rather
 * than writing the two side by side and having them refused as two writes at one place.
 *
 * <p>The two vocabularies a plan is made in, kept apart. A value fixed at a position is what stands
 * there; a narrowing is which case a position is, and says nothing about what stands under it. Put
 * in one map, a case would be a value nothing writes, and {@link ConstructionPlan} is where the two
 * are put together.
 *
 * <p>Positions of every element alike. A position under {@code [*]} names no element in
 * particular, so what is asked of it is asked of each element the value holds.
 *
 * @param fixed    the values that stand at positions inside the location, as those positions write
 *                 them, in the order they were asked for
 * @param required the narrowings that hold inside the location
 */
record DemandsInside(Map<TermPath, FixtureTemplate> fixed, Requirements required) {

    /** Nothing asked inside: the location is composed as its own type composes it. */
    static final DemandsInside NOTHING = new DemandsInside(Map.of(), Requirements.NONE);

    DemandsInside {
        fixed = Collections.unmodifiableMap(new LinkedHashMap<>(fixed));
    }

    /** Whether anything is asked inside at all. */
    boolean isEmpty() {
        return fixed.isEmpty() && required.refinements().isEmpty();
    }
}
