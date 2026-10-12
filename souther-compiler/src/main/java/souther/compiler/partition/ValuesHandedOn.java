package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ElementsTaken;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * What the parameters composed so far hand on to the containers of the ones after them: every value
 * standing at each position read, and every element of each container a demand is asked over.
 *
 * <p>Every one and not one. A position inside a container stands once in each element, and how many
 * of them a container after it is to hold turns on what was asked around it — each of them where
 * every element is asked about, and none where the container holds none. That is decided where the
 * demand is read ({@link ContentsAsked#resolvedFor}), so what is carried here is what was built,
 * with which element each value was read in.
 *
 * @param values   at each position read, the values standing there in what was built, each with
 *                 the elements taken to reach it
 * @param elements at each container a demand is asked over, the elements it holds, each as the
 *                 elements taken to reach it
 */
record ValuesHandedOn(Map<TermPath, List<Standing>> values,
                      Map<TermPath, List<ElementsTaken>> elements) {

    /** Nothing composed before. */
    static final ValuesHandedOn NONE = new ValuesHandedOn(Map.of(), Map.of());

    ValuesHandedOn {
        values = Map.copyOf(values);
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
        Map<TermPath, List<ElementsTaken>> bothElements = new LinkedHashMap<>(elements);
        bothElements.putAll(later.elements);
        return new ValuesHandedOn(bothValues, bothElements);
    }
}
