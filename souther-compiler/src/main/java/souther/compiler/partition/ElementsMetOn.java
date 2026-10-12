package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Which elements of the input a run makes a comparison on, where the comparison stands inside
 * closures an operation applies to the elements of containers the input holds.
 *
 * <p>Not whether a run makes the comparison at all, which is what stood on the way to it says and a
 * run through it records. This is which element: {@code List.any(x -> x > 0, xs)} applies its
 * closure to an element only where no element before it held, so on {@code [1, 0]} the comparison
 * is made on the first element and never on the second. A row standing at {@code 0} through its
 * second element stands where no run compared anything, and the run having got an answer out of the
 * comparison on the first element does not change that.
 *
 * <p>Said here and read off each reading of a row, because the order is the row's: which element
 * stops the operation is what the elements before it hold.
 */
public sealed interface ElementsMetOn {

    /**
     * Met on an element where, in each container the comparison's closures are applied over, no
     * element before the one a reading names stopped the operation.
     *
     * @param levels each container stopped short, the outermost first. None: a run that gets as
     *               far as the comparison makes it on every element a reading can name
     */
    record InOrder(List<StopsAt> levels) implements ElementsMetOn {

        public InOrder {
            levels = List.copyOf(levels);
        }
    }

    /**
     * Which elements the comparison is made on is not something the row's values say, for this
     * reason: a reading standing at a point through an element is not known to have been met there.
     */
    record NotSaid(ReadingGap why) implements ElementsMetOn {

        public NotSaid {
            Objects.requireNonNull(why, "what is not said is not said for a reason");
        }
    }

    /**
     * One container an operation stops short in.
     *
     * @param container where the container stands in the input
     * @param stops     what, said of an element of it, stops the operation there: what the
     *                  closure answers where it stops at the first that holds, and its denial
     *                  where it stops at the first that fails. A subject under
     *                  {@code container[*]} in it is that element's
     */
    record StopsAt(TermPath container, Proposition stops) {

        public StopsAt {
            Objects.requireNonNull(container, "an operation stops short in some container");
            Objects.requireNonNull(stops, "and at something");
        }
    }

    /** Every element a reading can name, which is what a comparison inside no such closure is. */
    ElementsMetOn EVERY = new InOrder(List.of());

    /** The same, inside one more closure that stops in {@code container} at what {@code stops}
     *  says of an element. */
    default ElementsMetOn stoppingIn(TermPath container, Proposition stops) {
        return switch (this) {
            case InOrder(var levels) -> {
                List<StopsAt> deeper = new ArrayList<>(levels);
                deeper.add(new StopsAt(container, stops));
                yield new InOrder(deeper);
            }
            case NotSaid _ -> this;
        };
    }
}
