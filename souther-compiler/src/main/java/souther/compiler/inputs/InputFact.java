package souther.compiler.inputs;

import java.math.BigInteger;
import java.util.Objects;

/**
 * A fact about the shape of the value of the input a proof rested on, beside the whole numbers it
 * holds at places ({@link AStopShown.NumberAt}): what a number alone does not say.
 *
 * <p>Said of the places of the input and never of one element by where it stands among others,
 * since {@link TermPath} puts no index in a path: a place inside a container is the place every
 * element of it stands at. An element is named by its index here, where the proof is of a value in
 * which the container holds it at that index.
 */
public sealed interface InputFact {

    /** The list at {@code list} holds exactly {@code length} elements. */
    record ListLength(TermPath list, int length) implements InputFact {

        public ListLength {
            Objects.requireNonNull(list, "a length is of some list");
            if (length < 0) {
                throw new IllegalArgumentException("a list holds none or more: " + length);
            }
        }
    }

    /** The element at {@code index} of the list at {@code list} is the whole number
     *  {@code number}. */
    record ListElement(TermPath list, int index, BigInteger number) implements InputFact {

        public ListElement {
            Objects.requireNonNull(list, "an element is of some list");
            Objects.requireNonNull(number, "an element holds some number");
            if (index < 0) {
                throw new IllegalArgumentException("an element is at an index from nought: "
                        + index);
            }
        }
    }
}
