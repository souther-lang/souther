package souther.compiler.program;

import souther.compiler.types.LeafScalar;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashSet;
import java.util.List;

/**
 * A type a value can leave as, at a behavior's boundary — projected from
 * {@link souther.compiler.check.BoundaryOutput}, which is where an answer's admission is decided.
 * As with {@link CheckedBoundaryInput}, this is the checked answer carried over, never a question
 * left for the arm that holds it.
 */
public sealed interface CheckedBoundaryOutput {

    /** The type in the language this shape stands for. */
    Type type();

    /** A scalar the boundary writes as itself. */
    record Scalar(LeafScalar scalar) implements CheckedBoundaryOutput {
        @Override
        public Type type() {
            return scalar.type();
        }
    }

    /** A type a model declared, encoded by the codec derived for it. */
    record Nominal(TypeSymbol name) implements CheckedBoundaryOutput {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }

    /** A list of them. */
    record ListOf(CheckedBoundaryOutput element) implements CheckedBoundaryOutput {
        @Override
        public Type type() {
            return Type.list(element.type());
        }
    }

    /** A set of them, written in the order their encoded members give. */
    record SetOf(CheckedBoundaryOutput element) implements CheckedBoundaryOutput {
        @Override
        public Type type() {
            return Type.set(element.type());
        }
    }

    /** A map of them, under a key the boundary can write as text. */
    record MapOf(MapKeyRepresentation key, CheckedBoundaryOutput value) implements CheckedBoundaryOutput {
        @Override
        public Type type() {
            return Type.map(key.type(), value.type());
        }
    }

    /**
     * The union a behavior answers with, whose members nobody named together, alongside the form
     * the set of them travels in — enumeration or discriminated, settled the same way and by the
     * same call as a named sum's (spec §sum-discrimination), so a reader of either asks nothing
     * about the cases that the other does not.
     */
    record Cases(List<TypeSymbol> members, CheckedAlternativesForm representation)
            implements CheckedBoundaryOutput {

        public Cases {
            members = List.copyOf(members);
        }

        @Override
        public Type type() {
            return Type.union(new LinkedHashSet<>(members));
        }
    }
}
