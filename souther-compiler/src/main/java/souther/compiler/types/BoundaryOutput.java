package souther.compiler.types;

import java.util.List;

/**
 * A type a value can leave as, at a behavior's boundary. The input's cases and one more: a behavior
 * may answer a union nobody named, which is the shape of its own answer.
 *
 * <p>As with {@link BoundaryInput}, this is the boundary's answer travelling rather than the question
 * being asked again — a reader switching over it is total over what can leave.
 */
public sealed interface BoundaryOutput {

    /** The type in the language this shape stands for. Answered per case rather than by switching, so
     *  a case added here cannot forget it. */
    Type type();

    /** A scalar the boundary writes as itself. */
    record Scalar(LeafScalar scalar) implements BoundaryOutput {
        @Override
        public Type type() {
            return scalar.type();
        }
    }

    /** A type a model declared, encoded by the codec derived for it. */
    record Nominal(TypeName name) implements BoundaryOutput {
        @Override
        public Type type() {
            return Type.ref(name);
        }
    }

    /** A list of them. */
    record ListOf(BoundaryOutput element) implements BoundaryOutput {
        @Override
        public Type type() {
            return Type.list(element.type());
        }
    }

    /** A set of them, written in the order their encoded members give. */
    record SetOf(BoundaryOutput element) implements BoundaryOutput {
        @Override
        public Type type() {
            return Type.set(element.type());
        }
    }

    /** A map of them, under a key the boundary can write as text. */
    record MapOf(BoundaryMapKey key, BoundaryOutput value) implements BoundaryOutput {
        @Override
        public Type type() {
            return Type.map(key.type(), value.type());
        }
    }

    /**
     * The union a behavior answers with, whose members nobody named together. Its encoder is the one
     * generated for the behavior's result, so what identifies it is the behavior rather than any of
     * the names — which is why the members travel and the class is asked for by the reader that knows
     * whose answer it is.
     */
    record Cases(List<TypeName> members) implements BoundaryOutput {
        public Cases {
            members = List.copyOf(members);
        }

        @Override
        public Type type() {
            return new Type.Union(new java.util.LinkedHashSet<>(members));
        }
    }
}
