package souther.compiler.check;

import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;

/**
 * A type a value can leave as, at a behavior's boundary. The input's cases and one more: a behavior
 * may answer a union nobody named, which is the shape of its own answer.
 *
 * <p>As with {@link BoundaryInput}, this is the boundary's answer travelling rather than the question
 * being asked again — a reader switching over it is total over what can leave. The two cases that
 * carry names are closed to this package for the reason given there.
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

    /** A type a model declared, encoded by the codec derived for it. Made where a name is admitted
     *  and nowhere else — see {@link BoundaryInput.Nominal}. */
    final class Nominal implements BoundaryOutput {

        private final CrossingNominal admitted;

        Nominal(CrossingNominal admitted) {
            this.admitted = admitted;
        }

        public TypeSymbol name() {
            return admitted.name();
        }

        @Override
        public Type type() {
            return Type.ref(name());
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Nominal n && admitted.equals(n.admitted);
        }

        @Override
        public int hashCode() {
            return Objects.hashCode(admitted);
        }

        @Override
        public String toString() {
            return "Nominal[name=" + name() + "]";
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
    record MapOf(CrossingMapKey key, BoundaryOutput value) implements BoundaryOutput {
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
     *
     * <p>Every member is a name, so this is closed the way {@link Nominal} is: a union assembled from
     * names nothing admitted would be a witness for an answer the boundary never allowed.
     *
     * <p>Names and not {@link CrossingNominal}s, though each member went through that admission.
     * What a witness is carried for is a reader that acts on the proposition being true; a reader
     * here asks which cases the answer has, and builds a type or a class name out of them. Carrying
     * the admission on into that would say a reader below still needs it, which is a claim about
     * them that is not so. If one comes to need it, this is where it changes.
     */
    final class Cases implements BoundaryOutput {

        private final List<TypeSymbol> members;

        Cases(List<TypeSymbol> members) {
            this.members = List.copyOf(members);
        }

        public List<TypeSymbol> members() {
            return members;
        }

        @Override
        public Type type() {
            return new Type.Union(new LinkedHashSet<>(members));
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Cases c && members.equals(c.members);
        }

        @Override
        public int hashCode() {
            return Objects.hashCode(members);
        }

        @Override
        public String toString() {
            return "Cases[members=" + members + "]";
        }
    }
}
