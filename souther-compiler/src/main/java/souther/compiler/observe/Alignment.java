package souther.compiler.observe;

import java.util.List;
import java.util.Map;

/**
 * Which part of an answer stands for which part of what a text stated.
 *
 * <p>What a report needs to write the two side by side. A map pairs its entries by key and a set
 * pairs its elements without an order, and both of those are questions about what being the same
 * value means — asked here by the step the comparison asks them by. A report that found them from
 * what the two are written as would be a second answer to that: two entries the comparison matched
 * but a rendering could not tell apart would be written as though the answer held neither.
 *
 * <p><b>Worked out when a report wants it, rather than kept by every comparison that holds.</b> A
 * verdict is asked of every row and nearly all of them hold; this is asked of the ones that did
 * not. So it is a second walk over the two values, under the rule the first one used and not a
 * rule of its own — which is what there is to hold to, and is why the one step that finds which
 * value a statement is about is written once and called from both.
 *
 * <p><b>A correspondence and not a verdict.</b> Nothing here says the two are the same; it says
 * which stood against which while that was being settled. A part that stands against nothing is
 * said as {@link Nothing}, which is what a reader writing it out has to know: there is no statement
 * putting it anywhere.
 *
 * <p>Over what the answer holds, because the answer is what is written out. Where the answer holds
 * something with no order of its own — a map, a set — neither side has a sequence to lend: a row
 * states a value rather than the way its source built one, and what it wrote was run, so what it
 * holds came out of a table too. So those are said as pairs ({@link Placed}, {@link Stood}): which
 * of the answer's parts goes with which of the statement's, and which of them go with nothing. Where
 * each of them is written is a report's to settle, and the counterpart is what tells it that two of
 * them belong in one place.
 */
public sealed interface Alignment {

    /** Nothing of the statement stands against this, so nothing about it is the text's. */
    record Nothing() implements Alignment {}

    /** A value with no parts, or one whose parts nothing here pairs. */
    record Leaf() implements Alignment {}

    /** A construction, by the name each field is held under. A field the statement does not write
     *  is absent from the map rather than held as {@link Nothing}, which reads the same and says it
     *  in the place a reader looks. */
    record Built(Map<String, Alignment> fields) implements Alignment {

        public Built {
            fields = Map.copyOf(fields);
        }
    }

    /** A list: one entry per element the answer holds, in the answer's own order, which is the
     *  value's. Each stands for the statement's element in the same place. */
    record InOrder(List<Alignment> byElement) implements Alignment {

        public InOrder {
            byElement = List.copyOf(byElement);
        }
    }

    /**
     * A set: the answer's elements that have a counterpart, each beside it, then the ones that do
     * not.
     *
     * <p>Apart from a list because a set holds no order and a list holds its own. Which element
     * stands for which is the comparison's answer either way; what differs is that for one of them
     * the answer's own sequence is a fact about the value and for the other it is a fact about the
     * numbers its elements hashed to — which is why a report puts these somewhere itself and the
     * counterpart is what says where.
     */
    record Unordered(List<Stood> written, List<ObservedValue> rest) implements Alignment {

        public Unordered {
            written = List.copyOf(written);
            rest = List.copyOf(rest);
        }
    }

    /** A mapping: the answer's entries that have a counterpart, each beside it, and then the ones
     *  that do not. */
    record Entries(List<Placed> written, List<ObservedValue.Entry> rest) implements Alignment {

        public Entries {
            written = List.copyOf(written);
            rest = List.copyOf(rest);
        }
    }

    /** One entry of the answer, beside the one of the statement it stands for. Both, because where
     *  the two go is decided by writing the statement's out, and which answer goes there is this. */
    record Placed(Asserted.Entry stated, ObservedValue.Entry entry, Alignment under) {}

    /** One element of the answer, beside the one of the statement it stands for. */
    record Stood(Asserted stated, ObservedValue element, Alignment under) {}
}
