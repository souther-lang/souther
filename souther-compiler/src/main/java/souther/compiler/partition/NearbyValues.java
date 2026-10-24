package souther.compiler.partition;

import souther.compiler.observe.ObservedValue;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * The values one step from a value a run was seen taking, for a search that looks beside where it
 * knows a run comes back.
 *
 * <p>One whole number is moved by one and everything else stays as it was, wherever the number sits:
 * inside a newtype, a field of a record, an element of a list. Only whole numbers have a value
 * directly beside them; a decimal has none, so none is invented for it, and a value with no whole
 * number in it has no neighbour here.
 */
final class NearbyValues {

    /** Every value that is {@code value} with one whole number in it one more or one less. */
    static List<ObservedValue> of(ObservedValue value) {
        List<ObservedValue> out = new ArrayList<>();
        collect(value, out);
        return out;
    }

    private static void collect(ObservedValue value, List<ObservedValue> out) {
        switch (value) {
            case ObservedValue.Integer whole -> {
                if (whole.value() != Long.MAX_VALUE) {
                    out.add(new ObservedValue.Integer(whole.value() + 1));
                }
                if (whole.value() != Long.MIN_VALUE) {
                    out.add(new ObservedValue.Integer(whole.value() - 1));
                }
            }
            case ObservedValue.Constructed built -> {
                // In the order of the names, so that which neighbour is tried first is the same on
                // every run.
                for (Map.Entry<String, ObservedValue> field
                        : new TreeMap<>(built.fields()).entrySet()) {
                    List<ObservedValue> inside = new ArrayList<>();
                    collect(field.getValue(), inside);
                    for (ObservedValue moved : inside) {
                        Map<String, ObservedValue> fields = new LinkedHashMap<>(built.fields());
                        fields.put(field.getKey(), moved);
                        out.add(new ObservedValue.Constructed(built.type(), fields));
                    }
                }
            }
            case ObservedValue.Sequence sequence -> {
                for (int at = 0; at < sequence.elements().size(); at++) {
                    List<ObservedValue> inside = new ArrayList<>();
                    collect(sequence.elements().get(at), inside);
                    for (ObservedValue moved : inside) {
                        List<ObservedValue> elements = new ArrayList<>(sequence.elements());
                        elements.set(at, moved);
                        out.add(new ObservedValue.Sequence(elements));
                    }
                }
            }
            default -> { }
        }
    }

    private NearbyValues() {}
}
