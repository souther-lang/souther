package souther.compiler.core;

import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

/**
 * How a value of one type is written into the metadata of an issue, for a type whose values can be:
 * a scalar the decoder library has a message form for, a list of such values, or a newtype over one.
 *
 * <p>Not every value that crosses the boundary has one. The decoder library writes in a message only
 * metadata whose type has a message form, and gives none to an optional, a map, a record or a
 * product; a constraint that would put such a value in its metadata does not type-check there. So a
 * constraint that reports the values it was handed carries the form they are reported in, and one
 * that cannot be given a form is not stated at all.
 *
 * <p>A newtype is reported as the value it wraps, which is how the boundary writes it and what its
 * equality reads. The value itself is still the one compared; only what the issue holds is the
 * wrapped one.
 */
public sealed interface MessageForm {

    /** The type in the language a value written in this form is of. */
    Type type();

    /** Whether a value of this form is written as something other than itself — whether a newtype
     *  stands anywhere in it. */
    boolean unwraps();

    /** A scalar, written as itself. */
    record Scalar(LeafScalar scalar) implements MessageForm {

        @Override
        public Type type() {
            return scalar.type();
        }

        @Override
        public boolean unwraps() {
            return false;
        }
    }

    /** A list, written as the list of its elements' forms. */
    record ListOf(MessageForm element) implements MessageForm {

        @Override
        public Type type() {
            return Type.list(element.type());
        }

        @Override
        public boolean unwraps() {
            return element.unwraps();
        }
    }

    /**
     * A value of the newtype {@code name}, written as the value it wraps.
     *
     * @param wraps the form of the value it wraps, which is a newtype's in turn for a newtype over
     *     another
     */
    record Newtype(TypeSymbol name, MessageForm wraps) implements MessageForm {

        @Override
        public Type type() {
            return Type.ref(name);
        }

        @Override
        public boolean unwraps() {
            return true;
        }
    }
}
