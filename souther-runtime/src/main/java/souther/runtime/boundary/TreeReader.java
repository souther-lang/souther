package souther.runtime.boundary;

import org.jspecify.annotations.Nullable;

import java.util.List;
import java.util.Map;

/**
 * What a decoder reads its input through: what a node is, an object's members, an array's elements,
 * and a scalar as the value its carrier holds (spec {@code [#a-decoder-reads-through-a-reader]}).
 *
 * <p>A reader answers what the tree holds and decides nothing about what is admitted. The carrier a
 * scalar is handed over in is asked by the decoder, so a reader that hands over a {@code double}
 * where the text wrote a decimal has not made the decoder read it: the decoder refuses it (spec
 * {@code [#a-boundary-scalar-is-read-not-converted]}). A reader of text MUST NOT keep one of two
 * values written under the same member name (spec {@code [#decoder-role]}).
 *
 * <p>{@link #PLAIN} reads maps, lists and the JDK's own values. A reader of another tree — a JSON
 * document's, a database row's — belongs to a decoder binding or to the application.
 */
public interface TreeReader {

    /** What a node of the tree is. */
    enum Shape {
        /** The tree's own null: what a decoder reads as absent. */
        NULL,
        /** A mapping from member names to values. */
        OBJECT,
        /** A sequence of values. */
        ARRAY,
        /** Anything else, read by {@link #scalar}. */
        SCALAR
    }

    /** What {@code node} is. */
    Shape shapeOf(Object node);

    /** The value of the member {@code name} of an {@link Shape#OBJECT}, or null where the object has
     *  no such member or holds the tree's null there. */
    @Nullable Object member(Object object, String name);

    /** The members of an {@link Shape#OBJECT}, in the order it holds them. A key is whatever the tree
     *  holds as one, which the decoder refuses where it is not a {@code String}; a value may be null. */
    Iterable<? extends Map.Entry<?, ?>> members(Object object);

    /** The elements of an {@link Shape#ARRAY}, in order, walked once. */
    Iterable<?> elements(Object array);

    /** The value a {@link Shape#SCALAR} holds, in the carrier the tree holds it in: a {@code String},
     *  a {@code Boolean}, a {@code Number}, a {@code java.time} value, or whatever else it is. */
    Object scalar(Object node);

    /** What {@code node} is, for a refusal to say what was found where something else was expected. */
    String describe(Object node);

    /** The reader of {@code java.util.Map}, {@code java.util.List} and every other value as itself. */
    TreeReader PLAIN = new TreeReader() {
        @Override
        public Shape shapeOf(Object node) {
            return node instanceof Map<?, ?> ? Shape.OBJECT
                    : node instanceof List<?> ? Shape.ARRAY
                    : Shape.SCALAR;
        }

        @Override
        public @Nullable Object member(Object object, String name) {
            return ((Map<?, ?>) object).get(name);
        }

        @Override
        public Iterable<? extends Map.Entry<?, ?>> members(Object object) {
            return ((Map<?, ?>) object).entrySet();
        }

        @Override
        public Iterable<?> elements(Object array) {
            return (List<?>) array;
        }

        @Override
        public Object scalar(Object node) {
            return node;
        }

        @Override
        public String describe(Object node) {
            return node.getClass().getSimpleName();
        }
    };
}
