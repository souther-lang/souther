package souther.compiler.program;

import souther.compiler.types.LeafScalar;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

/**
 * A type a value can arrive as, at a behavior's boundary — projected from
 * {@link souther.compiler.check.BoundaryInput}, which is where a parameter's admission is decided.
 * Holding one of these says a parameter of this shape was admitted; it does not carry the witness
 * that decided it, because deciding it again is not what a reader outside this compiler is for.
 *
 * <p>Every case here is the answer the checker settled, never a question left for the arm that
 * carries it: a reader switching over this is total over what can arrive and reads none of it off
 * {@link Type} alone, which is the whole of what {@link souther.compiler.check.BoundaryInput}'s own
 * doc says of it.
 */
public sealed interface CheckedBoundaryInput {

    /** The type in the language this shape stands for. */
    Type type();

    /** A scalar the boundary writes as itself. */
    record Scalar(LeafScalar scalar) implements CheckedBoundaryInput {
        @Override
        public Type type() {
            return scalar.type();
        }
    }

    /** A type a model declared, decoded by the codec derived for it. */
    record Nominal(TypeSymbol name) implements CheckedBoundaryInput {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }

    /** A list of them. */
    record ListOf(CheckedBoundaryInput element) implements CheckedBoundaryInput {
        @Override
        public Type type() {
            return Type.list(element.type());
        }
    }

    /** A set of them. */
    record SetOf(CheckedBoundaryInput element) implements CheckedBoundaryInput {
        @Override
        public Type type() {
            return Type.set(element.type());
        }
    }

    /** A map of them, under a key the boundary can write as text. */
    record MapOf(MapKeyRepresentation key, CheckedBoundaryInput value) implements CheckedBoundaryInput {
        @Override
        public Type type() {
            return Type.map(key.type(), value.type());
        }
    }
}
