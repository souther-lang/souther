package souther.compiler.inputs;

import souther.compiler.core.Core;
import souther.compiler.semantics.HowAClosureIsApplied;

import java.util.Objects;

/**
 * What an operation of the language handed a closure out of a container: the container, and which
 * part of what it holds.
 *
 * <p>The part is said beside the container rather than left to the reader of the closure. A closure
 * over a map is handed the key and the value, and the two are different positions of the input; a
 * name read as "something {@code container} holds" would be filed at whichever of them the reader
 * thought of first.
 *
 * <p>And how far the operation goes handing them over. What a closure states on the element after
 * the one {@code List.any} stopped at is stated on no run, so which applications there are is a
 * fact about the handing and not about the container.
 *
 * @param container the expression the container was handed as
 * @param part      which of the things it holds the closure was handed
 * @param applied   how far the operation goes applying the closure
 */
public record HeldIn(Core container, Part part, HowAClosureIsApplied applied) {

    /** Which part of what a container holds. */
    public enum Part {
        /** What a list or a set holds, or a map's value. */
        ELEMENT,
        /** The key a map files a value under. */
        KEY;

        /**
         * Where this part of the container at {@code container} stands.
         *
         * <p>Exhaustive over the parts, with no {@code default}: the one place a part becomes a
         * step of a path.
         */
        public TermPath of(TermPath container) {
            return switch (this) {
                case ELEMENT -> container.element();
                case KEY -> container.key();
            };
        }
    }

    public HeldIn {
        Objects.requireNonNull(container, "something held came from a container");
        Objects.requireNonNull(part, "and is some part of what it holds");
        Objects.requireNonNull(applied, "handed over some way");
    }
}
