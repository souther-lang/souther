package souther.compiler.meaning;

import souther.compiler.types.BindingId;

import java.util.Objects;

/**
 * Which value at a position a statement is about.
 *
 * <p>A position inside a container's elements, {@code xs[*].n}, says an element and not which one,
 * so two names for two elements of {@code xs} read {@code n} at one position and are two values.
 * The position is the subject's or the number's and stays so; this is held beside it, and two
 * statements alike at one position are one statement only where they are about one value.
 *
 * <p>Only what the names say. Two names may be handed one element on some run, so two of these are
 * never a proof that two values differ; one is one value.
 */
public sealed interface ValueIdentity {

    /** The value at the position, read through no name for an element: the row's own, or an
     *  element only a quantifier around it names. */
    ValueIdentity AT_THE_POSITION = new AtThePosition();

    /** What a spelling says of it beside the position: nothing, or which name it was read
     *  through. */
    String spelled();

    /** The value at the position, read through no name for an element. */
    record AtThePosition() implements ValueIdentity {

        @Override
        public String spelled() {
            return "";
        }
    }

    /**
     * The value at an element of a container that {@code name} stands for.
     *
     * <p>A name bound once is one value wherever it is read; a helper read at two calls binds a
     * name of each copy, which is another name.
     */
    record OfAnElement(BindingId name) implements ValueIdentity {

        public OfAnElement {
            Objects.requireNonNull(name, "an element read through a name is read through one");
        }

        @Override
        public String spelled() {
            return "@" + name;
        }
    }
}
