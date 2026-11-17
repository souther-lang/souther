package souther.compiler.inputs;

import java.util.List;
import java.util.Objects;

/**
 * Which position an expression holds the values of, in the way a total, a count or an order needs:
 * every occurrence of them, each as often, in the order written, one for each element, or something
 * exactly where the place holds something ({@link ElementQuestion#EVERY_OCCURRENCE},
 * {@link ElementQuestion#IN_THE_ORDER_WRITTEN}, {@link ElementQuestion#ONE_PER_ELEMENT},
 * {@link ElementQuestion#SAME_EMPTINESS}).
 *
 * <p>Not {@link ValuesAt}: the expression is not the values there, and no step into a field of it or a
 * narrowing of it to a case is offered. Made from the answer of the walk after the holding by
 * {@link InputReads}, which owns it.
 */
public sealed interface ValuesHeld {

    /** The expression holds the values of {@code path}, in the way the question asked. */
    record At(TermPath path) implements ValuesHeld {

        public At {
            Objects.requireNonNull(path, "a holding of a place is of somewhere");
        }
    }

    /** The expression holds the values of no place the walk follows. */
    record NotAPosition() implements ValuesHeld {}

    /** The expression holds the values of one of {@code among}, and nothing says which. */
    record MayStandAt(List<TermPath> among) implements ValuesHeld {

        public MayStandAt {
            among = List.copyOf(among);
            if (among.isEmpty()) {
                throw new IllegalArgumentException("a holding of one of several has some");
            }
        }
    }
}
