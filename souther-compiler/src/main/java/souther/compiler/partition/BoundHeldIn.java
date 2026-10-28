package souther.compiler.partition;

import souther.compiler.check.Location;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;

/**
 * The data a comparison is held against: the values a table bound is read out of.
 *
 * <p>A comparison a helper holds is one line wherever the helper is applied, and a bound it reads
 * out of a table it was handed is written once in that table. Two tables given to two calls are
 * two places to write a bound, and a bound written wrong in the second is shown by no row through
 * the first, however alike the bounds of the two come out. So the line is told apart by the data
 * its bound is read out of, which is what a row exercises, and never by the number.
 *
 * <p>The data and not the call. One table passed from two calls, or under another name, is one
 * location and one line; and a number a call writes as an argument is no data held here, so a
 * helper applied to different values is not told apart by them ({@link DataOrigins}).
 *
 * <p>More than one location is a bound read out of whichever of them a condition chooses. They are
 * one line together: which of them a row went through is not what a row at the bound says.
 *
 * <p><b>Which data it is, and nothing about what it is called.</b> The names are for a reader and
 * are kept beside the locations, outside what two of these are equal by, so one location reached
 * under two spellings is one.
 *
 * @param data   where the numbers of the bound are read out of, each once and in one order whatever
 *               the walk was, at least one place
 * @param called what each binding the places are rooted at is called, for a reader; no part of
 *               which data it is
 */
public record BoundHeldIn(List<Location> data, Map<BindingId, String> called) {

    public BoundHeldIn {
        if (data == null || data.isEmpty() || called == null) {
            throw new IllegalArgumentException("a bound held in data is read out of some: " + data);
        }
        data = data.stream().distinct().sorted(Comparator.comparing(Location::toString)).toList();
        called = Map.copyOf(called);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof BoundHeldIn that && data.equals(that.data);
    }

    @Override
    public int hashCode() {
        return data.hashCode();
    }

    /** The data as a reader names it: what each is rooted at is called, and the fields read from
     *  there, in one order whatever the walk was. The step into an element is left out, which is
     *  what tells a table from the record holding it and is no part of what a reader calls it. */
    public List<String> said() {
        List<String> out = new ArrayList<>();
        for (Location each : data) {
            StringBuilder sb = new StringBuilder(called.getOrDefault(each.root(),
                    String.valueOf(each.root())));
            for (String field : each.path()) {
                if (field.charAt(0) != '[') {
                    sb.append('.').append(field);
                }
            }
            if (!out.contains(sb.toString())) {
                out.add(sb.toString());
            }
        }
        return out;
    }

    /** The same, each with the binding that roots it, so that two bindings called alike are two
     *  entries. For a document, which is compared as it is written. */
    public List<String> identified() {
        return data.stream()
                .map(each -> each + " (" + called.getOrDefault(each.root(), "?") + ")").toList();
    }
}
