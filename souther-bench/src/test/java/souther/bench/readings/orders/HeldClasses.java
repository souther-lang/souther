package souther.bench.readings.orders;

import souther.compiler.partition.ClassOfAPosition;

import java.util.Map;
import java.util.Set;

/**
 * What a copy made, of a kind that has an order this compiler declares total.
 *
 * <p>Beside {@link Held}, whose copies are of things nothing declares an order for. What a reader
 * makes of these differs only in what it sorts them by.
 *
 * @param classes the classes of some positions
 * @param named   a name for each of them
 */
public record HeldClasses(Set<ClassOfAPosition> classes, Map<ClassOfAPosition, String> named) {

    public HeldClasses {
        classes = Set.copyOf(classes);
        named = Map.copyOf(named);
    }
}
