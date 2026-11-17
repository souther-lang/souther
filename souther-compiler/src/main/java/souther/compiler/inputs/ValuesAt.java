package souther.compiler.inputs;

import java.util.List;
import java.util.Objects;

/**
 * Where an expression stands: the expression is the values at the place, nothing made of them and
 * not some of them ({@link ElementQuestion#NAMED_POSITION}).
 *
 * <p>The one relation a field can be read at, an element taken of, a rule filed at, or a line
 * drawn on. A value made out of a place is {@link MadeFrom}, and what holds the elements of a place
 * in a count or an order is {@link ValuesHeld}; neither is offered these, and neither converts to
 * this. The step into a field is the walk's own, taken where it reads the position, so no step is
 * offered on the answer.
 *
 * <p>Made from the answer of the walk after a position by {@link InputReads}, which owns it.
 */
public sealed interface ValuesAt {

    /** The expression is the values at {@code path}. */
    record At(TermPath path) implements ValuesAt {

        public At {
            Objects.requireNonNull(path, "a position reached is somewhere");
        }
    }

    /**
     * The expression names no position of the input, which is a fact about the model. Where its
     * value came from is another question ({@link InputReads#cameFrom}).
     */
    record NotAPosition() implements ValuesAt {}

    /**
     * The expression stands at each of {@code among} on some run, and nothing here says which of
     * them any one read of it is: a fact about this compiler and not about the model.
     */
    record MayStandAt(List<TermPath> among) implements ValuesAt {

        public MayStandAt {
            among = List.copyOf(among);
            if (among.isEmpty()) {
                throw new IllegalArgumentException(
                        "a value that may stand somewhere may stand at some place");
            }
        }
    }
}
