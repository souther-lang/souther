package souther.compiler.check;

import souther.compiler.numeric.OrderedRuns;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The numbers the rules ask the value filed under a key to be among, at the places of the value
 * they name.
 *
 * <p>Where the value is a number the place is the value itself ({@link #THE_VALUE}); where it is a
 * record each place is a field of it, by the names of the fields on the way down, and a name that
 * wears one value is no step ({@link Location#isStep}). The numbers at a place are the runs they
 * lie in, so a number, a range and a range with a number left out are each said as themselves
 * ({@link OrderedRuns}).
 *
 * <p>What one rule asks of one place and what another asks of it are asked of one value, so the
 * numbers they leave are the ones both leave ({@link #meet}); and what is asked of two places of
 * the value is asked of two fields of it, which no number is in common between.
 *
 * @param at the numbers asked at each place, by the place
 */
public record ValueAsked(Map<List<String>, OrderedRuns> at) {

    /** The place of the value itself. */
    public static final List<String> THE_VALUE = List.of();

    public ValueAsked {
        at = Collections.unmodifiableMap(new LinkedHashMap<>(at));
    }

    /** The numbers {@code runs} asked at {@code place}. */
    public static ValueAsked at(List<String> place, OrderedRuns runs) {
        return new ValueAsked(Map.of(List.copyOf(place), runs));
    }

    /** What both this and {@code other} ask: at each place either names, the numbers both leave
     *  it. */
    public ValueAsked meet(ValueAsked other) {
        Map<List<String>, OrderedRuns> out = new LinkedHashMap<>(at);
        other.at.forEach((place, runs) -> out.merge(place, runs, OrderedRuns::meet));
        return new ValueAsked(out);
    }

    /** Whether some place of the value is left no number. */
    public boolean holdsNothing() {
        return at.values().stream().anyMatch(OrderedRuns::holdsNothing);
    }

    /**
     * Whether no one value can be what both this and {@code other} ask: some place both name is
     * left no number in common.
     *
     * <p>What two keys asked these of their values are, then, is two entries, since one entry holds
     * one value. Asked of places only one of them names, the two may be one value.
     */
    public boolean excludes(ValueAsked other) {
        for (Map.Entry<List<String>, OrderedRuns> each : at.entrySet()) {
            OrderedRuns there = other.at.get(each.getKey());
            if (there != null && each.getValue().meet(there).holdsNothing()) {
                return true;
            }
        }
        return false;
    }
}
