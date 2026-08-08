package souther.compiler.check;

import souther.compiler.types.BoundaryMapKey;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.Objects;

/**
 * A type a value can arrive as, at a behavior's boundary. Every case is a shape a decoder is built
 * for, so a reader that switches over this is total over what can arrive and has no arm for anything
 * else.
 *
 * <p>Which types those are is decided where the boundary's obligations are checked, and this is the
 * answer travelling rather than the question being asked again. A {@link Type} is the whole type
 * language: a tuple, a function, an optional, an anonymous union and a name the language keeps for
 * itself are all writable, and each is refused by the obligation that owns it. A reader handed a
 * {@code Type} can only know that by knowing all of them; a reader handed one of these knows it by
 * having one.
 *
 * <p>It lives beside {@link SignatureBoundary} because {@link Nominal} is closed to it: a name is a
 * thing the boundary either admits or refuses, and a case that could be assembled with a refused one
 * would be a witness of nothing. The cases that carry no name stay records — a scalar is a closed
 * set, and a list, a set or a map can only be built out of witnesses that were already admitted.
 *
 * <p>There is no case for an anonymous union. A parameter names a single type, so an input cannot be
 * one — which is why an input and an output are separate types here rather than one with an arm each
 * reader has to answer for.
 */
public sealed interface BoundaryInput {

    /** The type in the language this shape stands for. Answered per case rather than by switching, so
     *  a case added here cannot forget it. */
    Type type();

    /** A scalar the boundary writes as itself. */
    record Scalar(LeafScalar scalar) implements BoundaryInput {
        @Override
        public Type type() {
            return scalar.type();
        }
    }

    /**
     * A type a model declared, decoded by the codec derived for it.
     *
     * <p>Not a record: a record's canonical constructor is as accessible as the record, and a public
     * one would let a name the boundary refuses be assembled into a witness that every reader takes
     * for one the compiler stands behind. It is made where a name is admitted and nowhere else.
     */
    final class Nominal implements BoundaryInput {

        private final TypeName name;

        Nominal(TypeName name) {
            this.name = name;
        }

        public TypeName name() {
            return name;
        }

        @Override
        public Type type() {
            return Type.ref(name);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Nominal n && name.equals(n.name);
        }

        @Override
        public int hashCode() {
            return Objects.hashCode(name);
        }

        @Override
        public String toString() {
            return "Nominal[name=" + name + "]";
        }
    }

    /** A list of them. */
    record ListOf(BoundaryInput element) implements BoundaryInput {
        @Override
        public Type type() {
            return Type.list(element.type());
        }
    }

    /** A set of them. */
    record SetOf(BoundaryInput element) implements BoundaryInput {
        @Override
        public Type type() {
            return Type.set(element.type());
        }
    }

    /** A map of them, under a key the boundary can write as text. The key is the witness the map-key
     *  rule already answers with, so a key position cannot hold a list or an option. */
    record MapOf(BoundaryMapKey key, BoundaryInput value) implements BoundaryInput {
        @Override
        public Type type() {
            return Type.map(key.type(), value.type());
        }
    }
}
