package souther.compiler.ast;

import souther.compiler.types.Type;

/**
 * What the position an {@code example} or {@code fake} row writes a value at contributes to reading
 * it.
 *
 * <p>Two things, and they are not one. A position <em>says</em> what a notation that has no answer of
 * its own means there — which collection a row's brackets are, whether an unwritten optional field is
 * absent. A position also, sometimes, <em>requires</em> the value to be one of its type. An input is
 * both: it is handed to the model, so a value of another type is not one the model can be given. An
 * expectation is only the first: a row saying the behavior answers with something it does not is the
 * row doing its job, and what it wrote is compared rather than refused (E1905).
 *
 * <p>Held apart as a value because the two came to one parameter once already. Reading the position
 * for notation and checking against it are one call in a bidirectional checker, and a row that may
 * disagree with its position has no way to ask for the first without getting the second.
 */
public sealed interface RowPosition {

    /** The type this position contributes to reading what is written at it, or null where it has
     *  none to contribute. Never a constraint. */
    Type contextual();

    /** The type what is written here has to be, or null where it has to be nothing in particular. */
    Type required();

    /** What the row hands to the model: an input, a {@code with} value, a {@code fake}'s input or
     *  output. It is that value, so it is of that type. */
    record Supplies(Type type) implements RowPosition {

        @Override
        public Type contextual() {
            return type;
        }

        @Override
        public Type required() {
            return type;
        }
    }

    /** What the row asserts the behavior answers with. The type is read for what the notation does
     *  not say and for nothing else: a row writing a value of another type has written the
     *  disagreement it exists to report. */
    record Asserts(Type type) implements RowPosition {

        @Override
        public Type contextual() {
            return type;
        }

        @Override
        public Type required() {
            return null;
        }
    }
}
