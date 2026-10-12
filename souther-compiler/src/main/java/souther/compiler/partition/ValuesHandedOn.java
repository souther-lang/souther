package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ElementsTaken;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * What the parameters composed so far hand on to the containers of the ones after them: every value
 * standing at each position read, the one a demand asking one value there is handed, and every
 * element of each container a demand is asked over.
 *
 * <p>What stands at a position is one fact about what was built, and how many of those values a
 * container is handed is the demand's to say ({@link ContentsAsked#resolvedFor}) — so a position
 * read both ways is carried both ways. A demand asked over every element is handed the value read in
 * each element, or nothing where the container holds none; one asked of some element is handed the
 * value of the element the value was composed around.
 *
 * @param values   at each position read in each element, the values standing there in what was
 *                 built, each with the elements taken to reach it
 * @param chosen   at each position read as one value, that value: the only one there, or the one in
 *                 the element the value was composed around
 * @param elements at each container a demand is asked over, the elements it holds, each as the
 *                 elements taken to reach it
 */
record ValuesHandedOn(Map<TermPath, List<Standing>> values, Map<TermPath, Standing> chosen,
                      Map<TermPath, List<ElementsTaken>> elements) {

    /** Nothing composed before. */
    static final ValuesHandedOn NONE = new ValuesHandedOn(Map.of(), Map.of(), Map.of());

    ValuesHandedOn {
        values = Map.copyOf(values);
        chosen = Map.copyOf(chosen);
        elements = Map.copyOf(elements);
    }

    /**
     * One value standing at a position read.
     *
     * @param at    which element was taken at each container on the way to it
     * @param value the value, as a row writes it
     */
    record Standing(ElementsTaken at, FixtureTemplate value) {

        Standing {
            Objects.requireNonNull(at, "a value is reached through the elements it took");
            Objects.requireNonNull(value, "a value stands at the position");
        }
    }

    /** These, and what {@code later} hands on beside them. */
    ValuesHandedOn and(ValuesHandedOn later) {
        Map<TermPath, List<Standing>> bothValues = new LinkedHashMap<>(values);
        bothValues.putAll(later.values);
        Map<TermPath, Standing> bothChosen = new LinkedHashMap<>(chosen);
        bothChosen.putAll(later.chosen);
        Map<TermPath, List<ElementsTaken>> bothElements = new LinkedHashMap<>(elements);
        bothElements.putAll(later.elements);
        return new ValuesHandedOn(bothValues, bothChosen, bothElements);
    }
}
