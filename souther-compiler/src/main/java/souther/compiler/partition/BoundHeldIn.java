package souther.compiler.partition;

import souther.compiler.types.BindingId;

import java.util.Set;

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
 * binding and one line; and a number a call writes as an argument is no data held here, so a helper
 * applied to different values is not told apart by them.
 *
 * @param data the values the numbers of the bound are read out of, at least one
 */
public record BoundHeldIn(Set<Data> data) {

    /**
     * One value a bound is read out of.
     *
     * @param binding which binding holds it
     * @param name    what its binding is called, for a reader: the binding is the identity and the
     *                name is what the author wrote for it
     */
    public record Data(BindingId binding, String name) {

        public Data {
            if (binding == null || name == null) {
                throw new IllegalArgumentException(
                        "a value a bound is read out of is a binding, and called something: "
                                + binding + " " + name);
            }
        }
    }

    public BoundHeldIn {
        if (data == null || data.isEmpty()) {
            throw new IllegalArgumentException("a bound held in data is read out of some: " + data);
        }
        data = Set.copyOf(data);
    }
}
